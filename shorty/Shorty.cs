using System;
using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;
using System.Net;
using Microsoft.Dafny;
using Bpl = Microsoft.Boogie;

namespace shorty
{
    class NotValidException : Exception {}

    public class Shorty
    {
        public Program Program { get; private set; }

        private readonly AllRemovableTypes _allRemovableTypes;

        public ReadOnlyCollection<Wrap<Statement>> Asserts {
            get { return _allRemovableTypes.Asserts; }
        }

        public ReadOnlyCollection<Wrap<MaybeFreeExpression>> Invariants {
            get { return _allRemovableTypes.Invariants; }
        }

        public ReadOnlyCollection<Wrap<Expression>> Decreases {
            get { return _allRemovableTypes.Decreases; }
        }

        public ReadOnlyCollection<WildCardDecreases> DecreasesWildCards {
            get { return _allRemovableTypes.WildCardDecreaseses; }
        }

        public ReadOnlyCollection<Wrap<Statement>> LemmaCalls {
            get { return _allRemovableTypes.LemmaCalls; }
        }

        public ReadOnlyCollection<Wrap<Statement>> Calcs {
            get { return _allRemovableTypes.Calcs; }
        }

        public IRemover Remover { get; set; }

        #region Initialisation

        public Shorty(Program program, IRemover remover)
        {
            Contract.Requires(program != null);
            Program = program;
            if (!IsProgramValid()) {
                throw new NotValidException();
            }
            var removalTypeFinder = new RemovableTypeFinder(program);
            _allRemovableTypes = removalTypeFinder.FindRemovables();
            Remover = remover;
        }

        public Shorty(Program program)
        {
            Contract.Requires(program != null);
            Program = program;
            if (!IsProgramValid())
                throw new NotValidException();
            var removalTypeFinder = new RemovableTypeFinder(program);
            _allRemovableTypes = removalTypeFinder.FindRemovables();
            Remover = new OneAtATimeRemover(program);
        }

        #endregion

        #region Utility

        public void PrintProgram(TextWriter writer)
        {
            var dafnyPrinter = new Printer(writer);
            dafnyPrinter.PrintProgram(Program, false);
        }

        #endregion

        public SimplificationData FastRemoveAllRemovables()
        {
            var remover = new SimultaneousAllTypeRemover(Program);
            var simpData = remover.Remove(_allRemovableTypes);
            return simpData;
        }

        #region Lemma Calls

        public List<Statement> FindRemovableLemmaCalls()
        {
            var removableLemmaCalls = Remover.Remove(_allRemovableTypes.GetLemmaCallDictionary());
            foreach (var removableLemmaCall in removableLemmaCalls) {
                _allRemovableTypes.RemoveLemmaCall(removableLemmaCall);
            }
            return Wrap<Statement>.GetRemovables(removableLemmaCalls);
        }

        #endregion

        #region decreases

        public List<Expression> FindRemovableDecreases()
        {
            var removableDecreases = Remover.Remove(_allRemovableTypes.GetDecreasesDictionary());
            foreach (var removableDecrease in removableDecreases) {
                _allRemovableTypes.RemoveDecreases(removableDecrease);
            }
            //We also have to find removable wildcards which are stored differently
            WildCardDecreasesRemover wcdRemover = new WildCardDecreasesRemover(Program);
            var wildCardDecreases = wcdRemover.FindRemovableWildCards(_allRemovableTypes.WildCardDecreaseses.ToList());
            var expressions = Wrap<Expression>.GetRemovables(removableDecreases);

            foreach (var wildCardDecrease in wildCardDecreases) {
                _allRemovableTypes.RemoveWildCardDecreases(wildCardDecrease);
                expressions.Add(wildCardDecrease.Expression);
            }
            return expressions;
        }



        #endregion

        #region Invariants

        public List<MaybeFreeExpression> FindRemovableInvariants()
        {
            var removableInvariants = Remover.Remove(_allRemovableTypes.GetInvariantDictionary());
            foreach (var removableInvariant in removableInvariants) {
                _allRemovableTypes.RemoveInvariant(removableInvariant);
            }
            return Wrap<MaybeFreeExpression>.GetRemovables(removableInvariants);
        }

        public List<Tuple<MaybeFreeExpression, MaybeFreeExpression>> GetSimplifiedInvariants()
        {
            var simplifier = new Simplifier(Program);
            var wrappedInvariants = simplifier.GetSimplifiedItems(_allRemovableTypes.Invariants);
            var invariants = new List<Tuple<MaybeFreeExpression, MaybeFreeExpression>>();
            foreach (var wrappedInvariant in wrappedInvariants) {
                _allRemovableTypes.AddInvariant(wrappedInvariant.Item2, _allRemovableTypes.FindMemberFromInvariantWrap(wrappedInvariant.Item1));
                _allRemovableTypes.RemoveInvariant(wrappedInvariant.Item1);
                invariants.Add(new Tuple<MaybeFreeExpression, MaybeFreeExpression>(wrappedInvariant.Item1.Removable, wrappedInvariant.Item2.Removable));
            }
            return invariants;
        }


        public Dictionary<Method, List<List<MaybeFreeExpression>>> TestDifferentInvariantRemovals()
        {
            var removalOrderTester = new RemovalOrderTester<MaybeFreeExpression>(_allRemovableTypes.GetInvariantDictionary(), Program);
            return removalOrderTester.TestDifferentRemovals();
        }

        #endregion

        #region Asserts

        /// <summary>
        /// Removes unnecessary parts of asserts (e.g. combined by && where one part is not needed)
        /// </summary>
        /// <returns></returns>
        public List<Tuple<Statement, Statement>> GetSimplifiedAsserts()
        {
            var simplifier = new Simplifier(Program);
            var wrappedAsserts = simplifier.GetSimplifiedItems(_allRemovableTypes.Asserts);
            var asserts = new List<Tuple<Statement, Statement>>();
            foreach (var assert in wrappedAsserts) {
                _allRemovableTypes.AddAssert(assert.Item2, _allRemovableTypes.FindMemberFromAssertWrap(assert.Item1));
                _allRemovableTypes.RemoveAssert(assert.Item1);
                asserts.Add(new Tuple<Statement, Statement>(assert.Item1.Removable, assert.Item2.Removable));
            }
            return asserts;
        }

        public Dictionary<Method, List<List<Statement>>> TestDifferentAssertRemovals()
        {
            var removalOrderTester = new RemovalOrderTester<Statement>(_allRemovableTypes.GetAssertDictionary(), Program);
            return removalOrderTester.TestDifferentRemovals();
        }

        public List<Statement> FindRemovableAsserts()
        {
            var removedAsserts = Remover.Remove(_allRemovableTypes.GetAssertDictionary());
            foreach (var removedAssert in removedAsserts) {
                _allRemovableTypes.RemoveAssert(removedAssert);
            }
            if(!IsProgramValid())
                throw new Exception("Program invalid after assertion removal");
            return Wrap<Statement>.GetRemovables(removedAsserts);
        }

        #endregion

        #region Calc Statements

        public Tuple<List<Expression>, List<BlockStmt>, List<CalcStmt.CalcOp>, List<CalcStmt>> FindRemovableCalcs()
        {
            return FindRemovableCalcs(new CalcRemover(Program));
        }

        public Tuple<List<Expression>, List<BlockStmt>, List<CalcStmt.CalcOp>, List<CalcStmt>> FindRemovableCalcs(CalcRemover calcRemover)
        {
            return calcRemover.Remove(_allRemovableTypes.GetCalcDictionary());
        }

        #endregion

        #region validation

        public bool IsProgramValid()
        {
            var validator = new SimpleVerifier();
            return validator.IsProgramValid(Program);
        }

        #endregion
    }

    public class AllRemovableTypes
    {
        public readonly Dictionary<MemberDecl, RemovableTypesInMember> RemovableTypesInMethods = new Dictionary<MemberDecl, RemovableTypesInMember>();

        public ReadOnlyCollection<Wrap<Statement>> Asserts
        {
            get {
                var asserts = new List<Wrap<Statement>>();
                foreach (var removableTypes in RemovableTypesInMethods.Values)
                    asserts.AddRange(removableTypes.Asserts);
                return asserts.AsReadOnly();
            }
        }

        public ReadOnlyCollection<Wrap<MaybeFreeExpression>> Invariants
        {
            get {
                var invariants = new List<Wrap<MaybeFreeExpression>>();
                foreach (var removableTypes in RemovableTypesInMethods.Values)
                    invariants.AddRange(removableTypes.Invariants);
                return invariants.AsReadOnly();
            }
        }

        public ReadOnlyCollection<Wrap<Expression>> Decreases {
            get {
                var decreases = new List<Wrap<Expression>>();
                foreach (var removableTypes in RemovableTypesInMethods.Values)
                    decreases.AddRange(removableTypes.Decreases);
                return decreases.AsReadOnly();
            }
        }

        public ReadOnlyCollection<WildCardDecreases> WildCardDecreaseses {
            get {
                var wildCardDecreases = new List<WildCardDecreases>();
                foreach (var removableTypes in RemovableTypesInMethods.Values)
                    wildCardDecreases.AddRange(removableTypes.WildCardDecreaseses);
                return wildCardDecreases.AsReadOnly();
            }
        }

        public ReadOnlyCollection<Wrap<Statement>> LemmaCalls {
            get {
                var lemmaCalls = new List<Wrap<Statement>>();
                foreach (var removableTypes in RemovableTypesInMethods.Values)
                    lemmaCalls.AddRange(removableTypes.LemmaCalls);
                return lemmaCalls.AsReadOnly();
            }
        }

        public ReadOnlyCollection<Wrap<Statement>> Calcs {
            get {
                var calcs = new List<Wrap<Statement>>();
                foreach (var removableTypes in RemovableTypesInMethods.Values)
                    calcs.AddRange(removableTypes.Calcs);
                return calcs.AsReadOnly();
            }
        }

        public void AddMember(MemberDecl member)
        {
            if (!RemovableTypesInMethods.ContainsKey(member))
                RemovableTypesInMethods.Add(member, new RemovableTypesInMember(member));
        }

        #region Add methods

        public void AddAssert(Wrap<Statement> assert, MemberDecl member)
        {
            AddMember(member);
            RemovableTypesInMethods[member].Asserts.Add(assert);
        }

        public void AddInvariant(Wrap<MaybeFreeExpression> invariant, MemberDecl member)
        {
            AddMember(member);
            RemovableTypesInMethods[member].Invariants.Add(invariant);
        }

        public void AddDecreases(Wrap<Expression> decreases, MemberDecl member)
        {
            AddMember(member);
            RemovableTypesInMethods[member].Decreases.Add(decreases);
        }

        public void AddWildCardDecreases(WildCardDecreases wildCardDecreases, MemberDecl member)
        {
            AddMember(member);
            RemovableTypesInMethods[member].WildCardDecreaseses.Add(wildCardDecreases);
        }

        public void AddLemmaCall(Wrap<Statement> lemmaCall, MemberDecl member)
        {
            AddMember(member);
            RemovableTypesInMethods[member].LemmaCalls.Add(lemmaCall);
        }

        public void AddCalc(Wrap<Statement> calc, MemberDecl member)
        {
            AddMember(member);
            RemovableTypesInMethods[member].Calcs.Add(calc);
        }

        #endregion

        #region Removal Methods

        public void RemoveAssert(Wrap<Statement> assertWrap)
        {
            foreach (var removableTypesInMethods in RemovableTypesInMethods) {
                if (!removableTypesInMethods.Value.Asserts.Contains(assertWrap)) continue;
                removableTypesInMethods.Value.Asserts.Remove(assertWrap);
                return;
            }
        }

        public void RemoveInvariant(Wrap<MaybeFreeExpression> invariantWrap)
        {
            foreach (var removableTypesInMethods in RemovableTypesInMethods) {
                if (!removableTypesInMethods.Value.Invariants.Contains(invariantWrap)) continue;
                removableTypesInMethods.Value.Invariants.Remove(invariantWrap);
                return;
            }
        }

        public void RemoveDecreases(Wrap<Expression> decreasesWrap)
        {
            foreach (var removableTypesInMethods in RemovableTypesInMethods) {
                if (!removableTypesInMethods.Value.Decreases.Contains(decreasesWrap)) continue;
                removableTypesInMethods.Value.Decreases.Remove(decreasesWrap);
                return;
            }
        }

        public void RemoveWildCardDecreases(WildCardDecreases wildCardDecreases)
        {
            foreach (var removableTypesInMethods in RemovableTypesInMethods) {
                if (!removableTypesInMethods.Value.WildCardDecreaseses.Contains(wildCardDecreases)) continue;
                removableTypesInMethods.Value.WildCardDecreaseses.Remove(wildCardDecreases);
                return;
            }
        }

        public void RemoveLemmaCall(Wrap<Statement> lemmaCall)
        {
            foreach (var removableTypesInMethods in RemovableTypesInMethods) {
                if (!removableTypesInMethods.Value.LemmaCalls.Contains(lemmaCall)) continue;
                removableTypesInMethods.Value.LemmaCalls.Remove(lemmaCall);
                return;
            }
        }

        public void RemoveCalc(Wrap<Statement> calc)
        {
            foreach (var removableTypesInMethods in RemovableTypesInMethods) {
                if (!removableTypesInMethods.Value.Calcs.Contains(calc)) continue;
                removableTypesInMethods.Value.Calcs.Remove(calc);
                return;
            }
        }

        #endregion

        #region Get dictionaries

        public Dictionary<MemberDecl, List<Wrap<Statement>>> GetAssertDictionary()
        {
            var dictionary = new Dictionary<MemberDecl, List<Wrap<Statement>>>();
            foreach (var removableTypesInMethod in RemovableTypesInMethods.Values) {
                dictionary.Add(removableTypesInMethod.Member, removableTypesInMethod.Asserts);
            }
            return dictionary;
        }

        public Dictionary<MemberDecl, List<Wrap<MaybeFreeExpression>>> GetInvariantDictionary()
        {
            var dictionary = new Dictionary<MemberDecl, List<Wrap<MaybeFreeExpression>>>();
            foreach (var removableTypesInMethod in RemovableTypesInMethods.Values) {
                dictionary.Add(removableTypesInMethod.Member, removableTypesInMethod.Invariants);
            }
            return dictionary;
        }

        public Dictionary<MemberDecl, List<Wrap<Expression>>> GetDecreasesDictionary()
        {
            var dictionary = new Dictionary<MemberDecl, List<Wrap<Expression>>>();
            foreach (var removableTypesInMethod in RemovableTypesInMethods.Values) {
                dictionary.Add(removableTypesInMethod.Member, removableTypesInMethod.Decreases);
            }
            return dictionary;
        }

        public Dictionary<MemberDecl, List<Wrap<Statement>>> GetLemmaCallDictionary()
        {
            var dictionary = new Dictionary<MemberDecl, List<Wrap<Statement>>>();
            foreach (var removableTypesInMethod in RemovableTypesInMethods.Values) {
                dictionary.Add(removableTypesInMethod.Member, removableTypesInMethod.LemmaCalls);
            }
            return dictionary;
        }

        public Dictionary<MemberDecl, List<Wrap<Statement>>> GetCalcDictionary()
        {
            var dictionary = new Dictionary<MemberDecl, List<Wrap<Statement>>>();
            foreach (var removableTypesInMethod in RemovableTypesInMethods.Values) {
                dictionary.Add(removableTypesInMethod.Member, removableTypesInMethod.Calcs);
            }
            return dictionary;
        }

        #endregion

        public MemberDecl FindMemberFromAssertWrap(Wrap<Statement> wrap)
        {
            var dict = GetAssertDictionary();
            foreach (var member in dict.Keys) {
                if (dict[member].Contains(wrap))
                    return member;
            }
            return null;
        }

        public MemberDecl FindMemberFromInvariantWrap(Wrap<MaybeFreeExpression> wrap)
        {
            var dict = GetInvariantDictionary();
            foreach (var member in dict.Keys) {
                if (dict[member].Contains(wrap))
                    return member;
            }
            return null;
        }
    }

    public class RemovableTokenData
    {
        public Bpl.IToken StartToken { get; private set; }
        public Bpl.IToken EndToken { get; private set; }
        public string TypeOfRemovable { get; private set; }

        public RemovableTokenData(Bpl.IToken starToken, Bpl.IToken endToken, string typeOfRemovable)
        {
            StartToken = starToken;
            EndToken = endToken;
            TypeOfRemovable = typeOfRemovable;
        }

        public static List<RemovableTokenData> GetTokens(SimplificationData simpData)
        {
            List<RemovableTokenData> removableTokenData = new List<RemovableTokenData>();

            foreach (var removableAssert in simpData.RemovableAsserts) {
                removableTokenData.Add(new RemovableTokenData(removableAssert.Tok, removableAssert.EndTok, "Assert Statement"));
            }
            foreach (var invariant in simpData.RemovableInvariants) {
                //removableTokenData.Add(new RemovableTokenData(invariant.E.tok, invariant.E.)); //TODO: figure out how to get the end token/position
            }
            foreach (var removableDecrease in simpData.RemovableDecreases) {
                
            }
            foreach (var removableLemmaCall in simpData.RemovableLemmaCalls) {
                removableTokenData.Add(new RemovableTokenData(removableLemmaCall.Tok, removableLemmaCall.EndTok, "Lemma Call"));
            }
            foreach (var removableCalc in simpData.RemovableCalcs) {
                removableTokenData.Add(new RemovableTokenData(removableCalc.Tok, removableCalc.EndTok, "Calc Statement"));
            }
            foreach (var expression in simpData.SimplifiedCalcs.Item1) {
                
            }
            foreach (var blockStmt in simpData.SimplifiedCalcs.Item2) { //TODO pair up the hints and calcs.
                
            }
            foreach (var simplifiedAssert in simpData.SimplifiedAsserts) {
                //TODO get the removable parts of simplified asserts.
            }
            foreach (var simplifiedInvariant in simpData.SimplifiedInvariants) {
                
            }

            return removableTokenData;
        }
    }

    public class Dary
    {
        public List<RemovableTokenData> PurifyAll(Program program)
        {
            var shorty = new Shorty(program);

            return RemovableTokenData.GetTokens(shorty.FastRemoveAllRemovables());
        }

        public List<RemovableTokenData> PurifyMethod(Program program, MemberDecl member)
        {
            var methodRemover = new MethodRemover(program);
            var removables = methodRemover.FullSimplify(member);
            return RemovableTokenData.GetTokens(removables);
        }
    }
}
