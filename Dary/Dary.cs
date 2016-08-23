using System;
using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;
using System.Net;
using Microsoft.Dafny;
using Bpl = Microsoft.Boogie;

namespace Dary
{
    public class NotValidException : Exception {}

    internal class DaryController
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

        public DaryController(Program program, IRemover remover)
        {
            Contract.Requires(program != null);
            Program = program;
            if (!IsProgramValid())
                throw new NotValidException();
            var removalTypeFinder = new RemovableTypeFinder(program);
            _allRemovableTypes = removalTypeFinder.FindRemovables();
            Remover = remover;
        }

        public DaryController(Program program)
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

        public static List<DaryResult> GetTokens(SimplificationData simpData)
        {
            var removableTokenData = new List<DaryResult>();

            foreach (var removableAssert in simpData.RemovableAsserts)
                removableTokenData.Add(new DaryResult(removableAssert.Tok, removableAssert.EndTok, "Assert Statement"));
            foreach (var invariant in simpData.RemovableInvariants) 
                removableTokenData.Add(new DaryResult(invariant.E.tok, GetExpressionLength(invariant.E) + "invariant ".Length, "Invariant"));
            foreach (var removableDecrease in simpData.RemovableDecreases)
                removableTokenData.Add(new DaryResult(removableDecrease.tok, GetExpressionLength(removableDecrease) + "decreases ".Length, "Decreases Expression"));
            foreach (var removableLemmaCall in simpData.RemovableLemmaCalls) {
                int nameLength;
                try {
                    nameLength = (((removableLemmaCall.Rhss[0] as ExprRhs).Expr as ApplySuffix).Lhs as NameSegment).Name.Length;
                }
                catch (Exception) {
                    continue;
                }
                var startToken = new Bpl.Token(removableLemmaCall.Tok.line, removableLemmaCall.Tok.col - nameLength);
                removableTokenData.Add(new DaryResult(startToken, removableLemmaCall.EndTok, "Lemma Call"));
            }
            foreach (var removableCalc in simpData.RemovableCalcs)
                removableTokenData.Add(new DaryResult(removableCalc.Tok, removableCalc.EndTok, "Calc Statement"));

            // This way will return the calc statement so it can be replaced
            foreach (var calcStmt in simpData.SimplifiedCalcs.Item4)
                removableTokenData.Add(new DaryResult(calcStmt.Tok, calcStmt.EndTok, "Calc Statement", calcStmt));

            //this way will return the lines and hints -- commented out as there are issues getting the CalcOp

//            foreach (var line in simpData.SimplifiedCalcs.Item1)
//                removableTokenData.Add(new DaryResult(line.tok, GetExpressionLength(line), "Calc Line"));
//            foreach (var hint in simpData.SimplifiedCalcs.Item2)
//                removableTokenData.Add(new DaryResult(hint.Tok, hint.EndTok, "CalcStmt Hint"));

            foreach (var simplifiedAssert in simpData.SimplifiedAsserts)
                removableTokenData.Add(new DaryResult(simplifiedAssert.Item1.Tok, simplifiedAssert.Item1.EndTok, "Assert Statement", simplifiedAssert.Item2));
            foreach (var simplifiedInvariant in simpData.SimplifiedInvariants)
                removableTokenData.Add(new DaryResult(simplifiedInvariant.Item1.E.tok, GetExpressionLength(simplifiedInvariant.Item1.E) + "invariant ".Length, "Invariant", simplifiedInvariant.Item2));
            return removableTokenData;
        }

        private static int GetExpressionLength(Expression expr)
        {
            var sw = new StringWriter();
            var printer = new Printer(sw);
            printer.PrintExpression(expr, false);
            return sw.ToString().Length;
        }


    #endregion

        public SimplificationData FastRemoveAllRemovables()
        {
            var remover = new SimultaneousAllTypeRemover(Program);
            var simpData = remover.Remove(_allRemovableTypes);
            return simpData;
        }
        public SimplificationData FastRemoveAllRemovables(StopChecker stopChecker)
        {
            var remover = new SimultaneousAllTypeRemover(Program);
            var simpData = remover.Remove(_allRemovableTypes, stopChecker);
            return simpData;
        }
        public SimplificationData FastRemoveAllInMethods(StopChecker stopChecker, List<MemberDecl> members)
        {
            var remover = new SimultaneousAllTypeRemover(Program);
            var newAllRemovables = new AllRemovableTypes();
            foreach (var member in members) {
                if(!_allRemovableTypes.RemovableTypesInMethods.ContainsKey(member))
                    throw new Exception("Could not find the method");
                newAllRemovables.RemovableTypesInMethods.Add(member, _allRemovableTypes.RemovableTypesInMethods[member]);
            }
            var simpData = remover.Remove(newAllRemovables, stopChecker);
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

    internal class AllRemovableTypes
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

    /// <summary>
    /// A simple class with a variable Stop.
    /// An instance of this is passed to dary and
    /// setting Stop to true will terminate Dary after
    /// its next verification.
    /// </summary>
    public class StopChecker
    {
        public bool Stop = false;
    }

    /// <summary>
    /// A class containing the information returned from dary that
    /// can be used to remove and replace dafny code
    /// </summary>
    public class DaryResult
    {
        public Bpl.IToken StartTok { get; private set; }
        public int Length { get; private set; }
        public string TypeOfRemovable { get; private set; }
        public object Replace { get; private set; }

        public DaryResult(Bpl.IToken startToken, Bpl.IToken endToken, string typeOfRemovable)
        {
            StartTok = startToken;
            Length = endToken.pos - startToken.pos;
            TypeOfRemovable = typeOfRemovable;
            Replace = null;
        }

        public DaryResult(Bpl.IToken startToken, Bpl.IToken endToken, string typeOfRemovable, object replace)
        {
            StartTok = startToken;
            Length = endToken.pos - startToken.pos;
            TypeOfRemovable = typeOfRemovable;
            Replace = replace;
        }

        public DaryResult(Bpl.IToken startToken, int length, string typeOfRemovable)
        {
            StartTok = startToken;
            Length = length;
            TypeOfRemovable = typeOfRemovable;
            Replace = null;
        }

        public DaryResult(Bpl.IToken startToken, int length, string typeOfRemovable, object replace)
        {
            StartTok = startToken;
            Length = length;
            TypeOfRemovable = typeOfRemovable;
            Replace = replace;
        }


    }

    /// <summary>
    /// Dary removes unnecessary annotations from dafny programs and returns
    /// information allowing them to be removed from dafny source code
    /// </summary>
    public class Dary
    {
        private readonly StopChecker _stopChecker;
        public enum StatusEnum {Idle, Running}
        public StatusEnum Status = StatusEnum.Idle;

        private int _verifySnapshots;
        private int _errorTrace;
        private Bpl.OutputPrinter _printer;

        /// <param name="stopChecker">A StopChecker object to alert Dary to halt termination</param>
        public Dary(StopChecker stopChecker)
        {
            _stopChecker = stopChecker;
        }

        /// <summary>
        /// Finds unnecessary annotations throughout the whole dafny
        /// program and returns information on their locations
        /// </summary>
        /// <param name="program">The unresolved dafny program</param>
        /// <returns>A list of DaryResult objects</returns>
        public List<DaryResult> ProcessProgram(Program program)
        {
            Status = StatusEnum.Running;
            ApplyOptions();
            var daryController = new DaryController(program);
            var results = DaryController.GetTokens(daryController.FastRemoveAllRemovables(_stopChecker));
            RestoreOptions();
            Status = StatusEnum.Idle;
            return results;
        }

        /// <summary>
        /// Finds unnecessary annotations throughout the specified members
        /// in the dafny program and returns information on their locations
        /// </summary>
        /// <param name="program">The unresolved dafny program</param>
        /// <param name="members">The members to be checked for dead annotations</param>
        /// <returns>A list of DaryResult objects</returns>
        public List<DaryResult> ProcessMembers(Program program, List<MemberDecl> members)
        {
            Status = StatusEnum.Running;
            ApplyOptions();
            List<DaryResult> results;
            if (members.Count == 1) {
                var member = members[0];
                var methodRemover = new MethodRemover(program);
                var removables = methodRemover.FullSimplify(member);
                results = DaryController.GetTokens(removables);
            }
            else {
                var daryController = new DaryController(program);
                var removables = daryController.FastRemoveAllInMethods(_stopChecker, members);
                results = DaryController.GetTokens(removables);
            }
            RestoreOptions();
            Status = StatusEnum.Idle;
            return results;
        }

        private void ApplyOptions()
        {
            _errorTrace = DafnyOptions.O.ErrorTrace;
            DafnyOptions.O.ErrorTrace = 0;

            _verifySnapshots = DafnyOptions.O.VerifySnapshots;
            DafnyOptions.O.VerifySnapshots = 1;

            _printer = Bpl.ExecutionEngine.printer;
            Bpl.ExecutionEngine.printer = new InvisibleConsolePrinter();

            Contract.ContractFailed += ContractFailureHandler;
        }

        private void RestoreOptions()
        {
            DafnyOptions.O.ErrorTrace = _errorTrace;
            DafnyOptions.O.VerifySnapshots = _verifySnapshots;
            Bpl.ExecutionEngine.printer = _printer;

            Contract.ContractFailed -= ContractFailureHandler;
        }

        private static void ContractFailureHandler(Object obj, ContractFailedEventArgs args)
        {
            throw new ContractFailedException();
        }
    }
}
