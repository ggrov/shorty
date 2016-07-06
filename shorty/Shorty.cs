using System;
using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;
using Microsoft.Dafny;
using Bpl = Microsoft.Boogie;

namespace shorty
{
    internal class Shorty
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
        public IRemover Remover { get; set; }

        #region Initialisation

        public Shorty(Program program, IRemover remover)
        {
            Contract.Requires(program != null);
            Program = program;
            if (!IsProgramValid()) {
                throw new Exception("Initial program is not valid");
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
                throw new Exception("Initial program is not valid");
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
            var expressions = Wrap<Expression>.GetRemovables(removableDecreases);
            expressions.AddRange(FindRemovableWildCards());
            return expressions;
        }

        private List<Expression> FindRemovableWildCards()
        {
            var removableWildCards = new List<Expression>();
            foreach (var wcDecreases in _allRemovableTypes.WildCardDecreaseses)
                removableWildCards.AddRange(FindRemovableWildCards(wcDecreases).Item1);
            return removableWildCards;
        }

        private Tuple<List<Expression>, bool> FindRemovableWildCards(WildCardDecreases currentWildCardDecreases)
        {
            var removableWildCards = new List<Expression>();
            var safeToRemove = true;
            RemoveWildCardSubDecreases(currentWildCardDecreases, removableWildCards, ref safeToRemove);

            if (safeToRemove)
                RemoveWildCardDecreases(currentWildCardDecreases, removableWildCards, ref safeToRemove);

            return new Tuple<List<Expression>, bool>(removableWildCards, safeToRemove);
        }

        private void RemoveWildCardDecreases(WildCardDecreases currentWildCardDecreases, List<Expression> removableWildCards, ref bool safeToRemove)
        {
            var index = currentWildCardDecreases.ParentSpecification.Expressions.IndexOf(currentWildCardDecreases.Expression);
            currentWildCardDecreases.ParentSpecification.Expressions.Remove(currentWildCardDecreases.Expression);
            if (IsProgramValid()) {
                removableWildCards.Add(currentWildCardDecreases.Expression);
                if (currentWildCardDecreases.ParentWildCardDecreases == null)
                    _allRemovableTypes.RemoveWildCardDecreases(currentWildCardDecreases);
            }
            else {
                currentWildCardDecreases.ParentSpecification.Expressions.Insert(index, currentWildCardDecreases.Expression);
                safeToRemove = false;
            }
        }

        private void RemoveWildCardSubDecreases(WildCardDecreases wcd, List<Expression> removableWildCards, ref bool safeToRemove)
        {
            foreach (var subDec in wcd.SubDecreases) {
                var removableWCs = FindRemovableWildCards(subDec);
                removableWildCards.AddRange(removableWCs.Item1);
                if (safeToRemove)
                    safeToRemove = removableWCs.Item2;
            }
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

        #endregion

        #region Asserts

        public Dictionary<Method, List<List<AssertStmt>>> TestDifferentRemovals()
        {
            var returnData = new Dictionary<Method, List<List<AssertStmt>>>();
            foreach (var memberDecl in _allRemovableTypes.RemovableTypesInMethods.Keys) {
                var method = (Method) memberDecl;
                if(method == null) continue;
                var solutions = new List<List<AssertStmt>>();
                TestAssertRemovalOrdering(0, solutions, new List<AssertStmt>(), method);
                returnData.Add(method, solutions);
            }
            return returnData;
        }

        private void TestAssertRemovalOrdering(int index, List<List<AssertStmt>> solutions, List<AssertStmt> currentSolution, Method method)
        {
            if (index == _allRemovableTypes.RemovableTypesInMethods[method].Asserts.Count) {
                solutions.Add(new List<AssertStmt>(currentSolution));
                return;
            }
            var assert = (AssertStmt) _allRemovableTypes.Asserts[index].Removable;
            var parent = _allRemovableTypes.Asserts[index].ParentList;
            TryRemovingAssertForOrderingTest(assert, parent, method, index, currentSolution, solutions);
        }

        private void TryRemovingAssertForOrderingTest(AssertStmt assert, List<Statement> parent, Method method, int index, List<AssertStmt> currentSolution, List<List<AssertStmt>> solutions)
        {
            var assertPos = parent.IndexOf(assert);
            parent.Remove(assert);
            if (IsProgramValid()) {
                var newCurrentSolution = new List<AssertStmt>(currentSolution) {assert}; //create a copy of the currentSolution and add in the assert
                TestAssertRemovalOrdering(index + 1, solutions, newCurrentSolution, method);
                parent.Insert(assertPos, assert);
                TestAssertRemovalOrdering(index + 1, solutions, currentSolution, method);
            }
            else {
                parent.Insert(assertPos, assert);
                TestAssertRemovalOrdering(index + 1, solutions, currentSolution, method);
            }
        }

        /// <summary>
        /// Removes unnecessary parts of asserts (e.g. combined by && where one part is not needed)
        /// </summary>
        /// <returns></returns>
        public List<Tuple<AssertStmt, AssertStmt>> GetSimplifiedAsserts()
        {
            var simplifiedAsserts = new List<Tuple<AssertStmt, AssertStmt>>();
            foreach (var assertWrap in _allRemovableTypes.Asserts)
                TrySimplifyAssert(assertWrap, simplifiedAsserts);
            return simplifiedAsserts;
        }

        private void TrySimplifyAssert(Wrap<Statement> assertWrap, List<Tuple<AssertStmt, AssertStmt>> simplifiedAsserts)
        {
            var assert = (AssertStmt) assertWrap.Removable;
            var parent = assertWrap.ParentList;
            var binExpr = assert.Expr as BinaryExpr;
            if (binExpr != null)
                if (binExpr.Op != BinaryExpr.Opcode.And) return;

            var index = parent.IndexOf(assert);
            parent.Remove(assert);
            if (!IsProgramValid()) {
                SimplifyAssert(assertWrap, index, simplifiedAsserts);
            }
            else 
                Console.WriteLine("Whole assert can be completely removed separately");
        }

        private void SimplifyAssert(Wrap<Statement> assertWrap, int index, List<Tuple<AssertStmt, AssertStmt>> simplifiedAsserts)
        {
            var brokenAsserts = BreakAndReinsertAssert((AssertStmt) assertWrap.Removable, assertWrap.ParentList, index);
            brokenAsserts.Reverse();
            //Test to see which can be removed
            for (var assertNum = brokenAsserts.Count - 1; assertNum >= 0; assertNum--) {
                var brokenAssert = brokenAsserts[assertNum];
                if (!TryRemoveAssert(assertWrap)) continue;
                brokenAsserts.Remove(brokenAssert);
            }
            simplifiedAsserts.Add(new Tuple<AssertStmt, AssertStmt>((AssertStmt) assertWrap.Removable, CombineAsserts(brokenAsserts)));
        }

        private List<AssertStmt> BreakAndReinsertAssert(AssertStmt assert, List<Statement> parent, int index)
        {
            var brokenAsserts = BreakDownExpr(assert);
            foreach (var brokenAssert in brokenAsserts) {
                parent.Insert(index, brokenAssert);
            }
            return brokenAsserts;
        }

        private AssertStmt CombineAsserts(List<AssertStmt> brokenAsserts)
        {
            if (brokenAsserts.Count < 1) {
                return null;
            }
            if (brokenAsserts.Count == 1)
                return brokenAsserts[0];

            var assert = brokenAsserts[0];
            brokenAsserts.Remove(assert);
            var left = brokenAsserts[0].Expr;
            var right = CombineAsserts(brokenAsserts).Expr;
            var binExpr = new BinaryExpr(left.tok, BinaryExpr.Opcode.And, left, right);
            var newAssert = new AssertStmt(assert.Tok, assert.EndTok, binExpr, assert.Attributes);
            return newAssert;
        }

        private List<AssertStmt> BreakDownExpr(AssertStmt assert)
        {
            var brokenAsserts = new List<AssertStmt>();
            var binaryExpr = assert.Expr as BinaryExpr;
            if (binaryExpr == null || binaryExpr.Op != BinaryExpr.Opcode.And) {
                brokenAsserts.Add(assert);
                return brokenAsserts;
            }
            var newAssert = new AssertStmt(binaryExpr.tok, assert.EndTok, binaryExpr.E0, assert.Attributes);
            var newAssert2 = new AssertStmt(binaryExpr.tok, assert.EndTok, binaryExpr.E1, assert.Attributes);
            brokenAsserts.AddRange(BreakDownExpr(newAssert));
            brokenAsserts.AddRange(BreakDownExpr(newAssert2));
            return brokenAsserts;
        }

        public List<Statement> FindRemovableAsserts()
        {
            var removedAsserts = Remover.Remove(_allRemovableTypes.GetAssertDictionary());
            foreach (var removedAssert in removedAsserts) {
                _allRemovableTypes.RemoveAssert(removedAssert);
            }
            return Wrap<Statement>.GetRemovables(removedAsserts);
        }

        private bool TryRemoveAssert(Wrap<Statement> assertWrap)
        {
            var parent = assertWrap.ParentList;
            var assert = assertWrap.Removable;
            var position = parent.IndexOf(assert);
            parent.Remove(assert);
            if (IsProgramValid()) {
                _allRemovableTypes.RemoveAssert(assertWrap);
                return true;
            }
            parent.Insert(position, assert);
            return false;
        }

        #endregion

        #region validation

        public bool IsProgramValid()
        {
            var validator = new SimpleValidator();
            return validator.IsProgramValid(Program);
        }

        #endregion
    }

    internal class SimpleValidator
    {
        public void BoogieErrorInformation(Bpl.ErrorInformation errorInfo) {}

        private Program CloneProgram(Program program)
        {
            var cloner = new Cloner();
            var moduleDecl = new LiteralModuleDecl(cloner.CloneModuleDefinition(program.DefaultModuleDef, program.Name), null);
            return new Program(program.FullName, moduleDecl, program.BuiltIns, new ConsoleErrorReporter());
        }

        public bool IsProgramValid(Program program)
        {
            try {
                var programId = "main_program_id";
                var stats = new Bpl.PipelineStatistics();
                var translator = new Translator(new ConsoleErrorReporter());
                var programCopy = CloneProgram(program);
                var resolver = new Resolver(programCopy);
                resolver.ResolveProgram(programCopy);
                var boogieProgram = translator.Translate(programCopy);
                var bplFileName = "bplFile";
                Bpl.LinearTypeChecker ltc;
                Bpl.CivlTypeChecker ctc;

                var oc = Bpl.ExecutionEngine.ResolveAndTypecheck(boogieProgram, bplFileName, out ltc, out ctc);
                if (oc != Bpl.PipelineOutcome.ResolvedAndTypeChecked) return false;

                Bpl.ExecutionEngine.EliminateDeadVariables(boogieProgram);
                Bpl.ExecutionEngine.CollectModSets(boogieProgram);
                Bpl.ExecutionEngine.CoalesceBlocks(boogieProgram);
                Bpl.ExecutionEngine.Inline(boogieProgram);
                Bpl.ErrorReporterDelegate er = BoogieErrorInformation;

                oc = Bpl.ExecutionEngine.InferAndVerify(boogieProgram, stats, programId, er);

                var allOk = stats.ErrorCount == 0 && stats.InconclusiveCount == 0 && stats.TimeoutCount == 0 && stats.OutOfMemoryCount == 0;
                Console.WriteLine(allOk ? "Verification Successful" : "Verification failed");
                return oc == Bpl.PipelineOutcome.VerificationCompleted && allOk;
            }
            catch (Exception e) {
                Console.WriteLine("Verification failed: " + e.Message);
                return false;
            }
        }
    }

    class AllRemovableTypes
    {
        public readonly Dictionary<MemberDecl, RemovableTypesInMember> RemovableTypesInMethods = new Dictionary<MemberDecl, RemovableTypesInMember>();

        public ReadOnlyCollection<Wrap<Statement>> Asserts {
            get {
                var asserts = new List<Wrap<Statement>>();
                foreach (var removableTypes in RemovableTypesInMethods.Values)
                    asserts.AddRange(removableTypes.Asserts);
                return asserts.AsReadOnly();
            }
        }

        public ReadOnlyCollection<Wrap<MaybeFreeExpression>> Invariants {
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

        #endregion
    }

    class RemovableTypesInMember
    {
        public MemberDecl Member { get; private set; }
        public readonly List<Wrap<Statement>> Asserts = new List<Wrap<Statement>>();
        public readonly List<Wrap<MaybeFreeExpression>> Invariants = new List<Wrap<MaybeFreeExpression>>();
        public readonly List<Wrap<Expression>> Decreases = new List<Wrap<Expression>>();
        public readonly List<WildCardDecreases> WildCardDecreaseses = new List<WildCardDecreases>();
        public readonly List<Wrap<Statement>> LemmaCalls = new List<Wrap<Statement>>();

        public RemovableTypesInMember(MemberDecl member)
        {
            Member = member;
        }
    }

    public class Wrap<T>
    {
        public T Removable { get; protected set; }
        public List<T> ParentList { get; private set; }

        public Wrap(T removable, List<T> parentList)
        {
            Removable = removable;
            ParentList = parentList;
        }

        public static List<T> GetRemovables(List<Wrap<T>> wrapList)
        {
            var removables = new List<T>();
            foreach (var wrap in wrapList) {
                removables.Add(wrap.Removable);
            }
            return removables;
        }
    }

    internal class WildCardDecreases
    {
        public readonly Expression Expression;
        public readonly Specification<Expression> ParentSpecification;
        public readonly WildCardDecreases ParentWildCardDecreases;
        public readonly List<WildCardDecreases> SubDecreases = new List<WildCardDecreases>();

        public int Count {
            get { return 1 + SubDecreases.Sum(wildCardDecreases => wildCardDecreases.Count); }
        }

        public WildCardDecreases(Expression decreasesExpression, Specification<Expression> parentSpecification, WildCardDecreases parentWildCardDecreases)
        {
            Expression = decreasesExpression;
            ParentSpecification = parentSpecification;
            ParentWildCardDecreases = parentWildCardDecreases;
        }
    }

    internal interface IRemover
    {
        List<Wrap<T>> Remove<T>(Dictionary<MemberDecl, List<Wrap<T>>> memberWrapDictionary);
    }

    internal class OneAtATimeRemover : IRemover
    {
        private readonly Program _program;

        public OneAtATimeRemover(Program program)
        {
            _program = program;
        }

        public List<Wrap<T>> Remove<T>(Dictionary<MemberDecl, List<Wrap<T>>> memberWrapDictionary)
        {
            var removableWraps = new List<Wrap<T>>();
            foreach (var wraps in memberWrapDictionary.Values) {
                removableWraps.AddRange(RemoveWraps(wraps.AsReadOnly()));
            }
            return removableWraps;
        }

        List<Wrap<T>> RemoveWraps<T>(ReadOnlyCollection<Wrap<T>> wraps)
        {
            var removableWraps = new List<Wrap<T>>();
            foreach (var wrap in wraps) {
                if (!TryRemove(wrap)) continue;
                removableWraps.Add(wrap);
            }
            return removableWraps;
        }

        private bool TryRemove<T>(Wrap<T> wrap)
        {
            var parentBody = wrap.ParentList;
            var removable = wrap.Removable;
            var index = parentBody.IndexOf(removable);
            parentBody.Remove(removable);
            if (IsProgramValid(_program)) {
                return true;
            }
            parentBody.Insert(index, removable);
            return false;
        }

        private static bool IsProgramValid(Program program)
        {
            var validator = new SimpleValidator();
            return validator.IsProgramValid(program);
        }
    }
}
