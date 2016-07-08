using System;
using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;
using System.Net;
using System.Runtime.CompilerServices;
using Microsoft.Dafny;
using Bpl = Microsoft.Boogie;
using Type = System.Type;

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
            Contract.ContractFailed += Testere;
        }

        private void Testere(object sender, ContractFailedEventArgs e)
        {
            Console.WriteLine("djsnf'klsanf'kewanfwa");
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

        /// <summary>
        /// Removes unnecessary parts of asserts (e.g. combined by && where one part is not needed)
        /// </summary>
        /// <returns></returns>
        public List<Tuple<Statement, Statement>> GetSimplifiedAsserts()
        {
            Simplifier simplifier = new Simplifier(Program);
            return simplifier.GetSimplifiedItems(_allRemovableTypes.Asserts);
        }

        public Dictionary<Method, List<List<Statement>>> TestDifferentAssertRemovals()
        {
            RemovalOrderTester<Statement> removalOrderTester = new RemovalOrderTester<Statement>(_allRemovableTypes.GetAssertDictionary(), Program);
            return removalOrderTester.TestDifferentRemovals();
        }

        public List<Statement> FindRemovableAsserts()
        {
            var removedAsserts = Remover.Remove(_allRemovableTypes.GetAssertDictionary());
            foreach (var removedAssert in removedAsserts) {
                _allRemovableTypes.RemoveAssert(removedAssert);
            }
            return Wrap<Statement>.GetRemovables(removedAsserts);
        }

        #endregion

        #region Calc Statements

        public List<Tuple<Expression, BlockStmt>> FindRemovableCalcs()
        {
            return FindRemovableCalcs(new CalcRemover(Program));
        }

        public List<Tuple<Expression, BlockStmt>> FindRemovableCalcs(CalcRemover calcRemover)
        {
            
            var removedCalcs = calcRemover.Remove(_allRemovableTypes.GetCalcDictionary());
            var removedCalcTuples = new List<Tuple<Expression, BlockStmt>>();
            foreach (var removedCalc in removedCalcs) {
                _allRemovableTypes.RemoveCalc(removedCalc);
                removedCalcTuples.Add(new Tuple<Expression, BlockStmt>(removedCalc.LineWrap.Removable, removedCalc.HintWrap.Removable));
            }
            return removedCalcTuples;
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

    internal class SimpleVerifier
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
            return IsProgramValid(program, null);
        }

        public bool IsProgramValid(Program program, Bpl.ErrorReporterDelegate errorDelegate)
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

                oc = Bpl.ExecutionEngine.InferAndVerify(boogieProgram, stats, programId, errorDelegate);

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

        public ReadOnlyCollection<CalcWrap> Calcs {
            get {
                var calcLines = new List<CalcWrap>();
                foreach (var removableTypes in RemovableTypesInMethods.Values)
                    calcLines.AddRange(removableTypes.Calcs);
                return calcLines.AsReadOnly();
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

        public void AddCalc(CalcWrap calc, MemberDecl member)
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

        public void RemoveCalc(CalcWrap calc)
        {
            foreach (var removableTypesInMethods in RemovableTypesInMethods)
            {
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

        public Dictionary<MemberDecl, List<CalcWrap>> GetCalcDictionary()
        {
            var dictionary = new Dictionary<MemberDecl, List<CalcWrap>>();
            foreach (var removableTypesInMethod in RemovableTypesInMethods.Values) {
                dictionary.Add(removableTypesInMethod.Member, removableTypesInMethod.Calcs);
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
        public readonly List<CalcWrap> Calcs = new List<CalcWrap>();

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

    public class CalcWrap
    {
        public readonly Wrap<BlockStmt> HintWrap;
        public readonly Wrap<Expression> LineWrap;

        public CalcWrap(Wrap<BlockStmt> hint, Wrap<Expression> line)
        {
            HintWrap = hint;
            LineWrap = line;
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

    class CalcRemover
    {
        SimpleVerifier verifier = new SimpleVerifier();
        private Program _program;

        public CalcRemover(Program program)
        {
            _program = program;
        }

        public List<CalcWrap> Remove(Dictionary<MemberDecl, List<CalcWrap>> memberWrapDictionary)
        {
            var removableWraps = new List<CalcWrap>();
            foreach (var wraps in memberWrapDictionary.Values)
            {
                removableWraps.AddRange(RemoveWraps(wraps));
            }
            return removableWraps;
        }

        public List<CalcWrap> RemoveWraps(List<CalcWrap> wraps)
        {
            var removableWraps = new List<CalcWrap>();
            foreach (var wrap in wraps) {
                if(!TryRemove(wrap.LineWrap, wrap.HintWrap)) continue;
                removableWraps.Add(wrap);
            }
            return removableWraps;

        }

        public bool TryRemove(Wrap<Expression> line, Wrap<BlockStmt> hint)
        {
            var lineIndex = line.ParentList.IndexOf(line.Removable);
            var hintIndex = hint.ParentList.IndexOf(hint.Removable);
            // We should also never be trying to remove the first or last line
            Contract.Assert(lineIndex != 0);
            Contract.Assert(lineIndex != line.ParentList.Count - 1);
            line.ParentList.Remove(line.Removable);
            hint.ParentList.Remove(hint.Removable);
            if (verifier.IsProgramValid(_program))
            {
                return true;
            }
            line.ParentList.Insert(lineIndex, line.Removable);
            hint.ParentList.Insert(hintIndex, hint.Removable);
            //TODO: try and remove everything inside the hint
            return false;
        }
    }

    internal interface IRemover
    {
        List<Wrap<T>> Remove<T>(Dictionary<MemberDecl, List<Wrap<T>>> memberWrapDictionary);
        //bool TryRemove<T>(Wrap<T> wrap);
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

        public bool TryRemove<T>(Wrap<T> wrap)
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
            var validator = new SimpleVerifier();
            return validator.IsProgramValid(program);
        }
    }

    internal class SimiltaneousMethodRemover : IRemover
    {
        // Goes though each method, removes one thing then verifies and reinserts from the error messages
        private readonly Program _program;
        private readonly SimpleVerifier _simpleVerifier = new SimpleVerifier();

        internal class SimilRemoverStorage<T>
        {
            public Dictionary<MemberDecl, Tuple<Wrap<T>, int>> LastRemovedItem = new Dictionary<MemberDecl, Tuple<Wrap<T>, int>>();

            public void ErrorInformation(Bpl.ErrorInformation errorInfo)
            {
                MemberDecl member = FindMethod(errorInfo.Tok.pos);
                LastRemovedItem[member].Item1.ParentList.Insert(LastRemovedItem[member].Item2, LastRemovedItem[member].Item1.Removable);
                LastRemovedItem.Remove(member);
            }

            private MemberDecl FindMethod(int pos)
            {
                foreach (var member in LastRemovedItem.Keys) {
                    if (member.BodyStartTok.pos <= pos && member.BodyEndTok.pos >= pos) {
                        return member;
                    }
                }
                throw new Exception("Could not find method");
            }
        }

        public SimiltaneousMethodRemover(Program program)
        {
            _program = program;
        }

        public List<Wrap<T>> Remove<T>(Dictionary<MemberDecl, List<Wrap<T>>> memberWrapDictionary)
        {
            List<Wrap<T>> removableWraps = new List<Wrap<T>>();
            bool finished = false;
            SimilRemoverStorage<T> similRemover = new SimilRemoverStorage<T>();
            int index = 0;
            while (!finished) {
                finished = true;
                foreach (var method in memberWrapDictionary.Keys) {
                    if(memberWrapDictionary[method].Count <= index) continue;
                    similRemover.LastRemovedItem.Add(method, RemoveOne(memberWrapDictionary[method][index]));
                    finished = false;
                }
                index++;
                _simpleVerifier.IsProgramValid(_program, similRemover.ErrorInformation);
                foreach (var value in similRemover.LastRemovedItem.Values) {
                    removableWraps.Add(value.Item1);
                }
                similRemover.LastRemovedItem = new Dictionary<MemberDecl, Tuple<Wrap<T>, int>>();
            }
            return removableWraps;
        }

        private Tuple<Wrap<T>,int> RemoveOne<T>(Wrap<T> wrap)
        {
            int position = wrap.ParentList.IndexOf(wrap.Removable);
            wrap.ParentList.Remove(wrap.Removable);
            return new Tuple<Wrap<T>, int>(wrap, position);
        }
    }

    internal class RemovalOrderTester<T>
    {
        private readonly Dictionary<MemberDecl, List<Wrap<T>>> _memberWrapDictionary;
        private readonly Program _program;

        public RemovalOrderTester(Dictionary<MemberDecl, List<Wrap<T>>> memberWrapDictionary, Program program)
        {
            _memberWrapDictionary = memberWrapDictionary;
            _program = program;
        }

        public Dictionary<Method, List<List<T>>> TestDifferentRemovals()
        {
            var returnData = new Dictionary<Method, List<List<T>>>();
            foreach (var memberDecl in _memberWrapDictionary.Keys) {
                var method = (Method) memberDecl;
                if (method == null) continue;
                var solutions = new List<List<T>>();
                TestRemovalOrdering(0, solutions, new List<T>(), method);
                returnData.Add(method, solutions);
            }
            return returnData;
        }

        private void TestRemovalOrdering(int index, List<List<T>> solutions, List<T> currentSolution, Method method)
        {
            if (index == _memberWrapDictionary[method].Count) {
                solutions.Add(new List<T>(currentSolution));
                return;
            }
            var item = _memberWrapDictionary[method][index].Removable;
            var parent = _memberWrapDictionary[method][index].ParentList;
            TryRemovingItemForOrderingTest(item, parent, method, index, currentSolution, solutions);
        }

        private void TryRemovingItemForOrderingTest(T item, List<T> parent, Method method, int index, List<T> currentSolution, List<List<T>> solutions)
        {
            var assertPos = parent.IndexOf(item);
            parent.Remove(item);
            var validator = new SimpleVerifier();
            if (validator.IsProgramValid(_program)) {
                var newCurrentSolution = new List<T>(currentSolution) {item}; //create a copy of the currentSolution and add in the item
                TestRemovalOrdering(index + 1, solutions, newCurrentSolution, method);
                parent.Insert(assertPos, item);
                TestRemovalOrdering(index + 1, solutions, currentSolution, method);
            }
            else {
                parent.Insert(assertPos, item);
                TestRemovalOrdering(index + 1, solutions, currentSolution, method);
            }
        }
    }

    internal class Simplifier
    {
        private readonly OneAtATimeRemover _remover;
        private readonly SimpleVerifier _verifier = new SimpleVerifier();
        private readonly Program _program;

        public Simplifier(Program program)
        {
            _program = program;
            _remover = new OneAtATimeRemover(program);
        }

        public List<Tuple<T, T>> GetSimplifiedItems<T>(IEnumerable<Wrap<T>> itemWraps)
        {
            var simplifiedItems = new List<Tuple<T, T>>();
            foreach (var wrap in itemWraps)
                simplifiedItems.Add(TrySimplifyItem(wrap));
            return simplifiedItems;
        }

        public Tuple<T, T> TrySimplifyItem<T>(Wrap<T> wrap)
        {
            var item = wrap.Removable;
            var parent = wrap.ParentList;
            var binExpr = GetExpr(wrap.Removable) as BinaryExpr;
            if (binExpr != null)
                if (binExpr.Op != BinaryExpr.Opcode.And) return null;

            var index = parent.IndexOf(item);
            parent.Remove(item);
            if (!_verifier.IsProgramValid(_program))
            {
                return SimplifyItem(wrap, index);
            }
            Console.WriteLine("Whole assert can be completely removed separately"); //TODO figure out what to do here (remove from _removableItems?)
            return null;
        }

        private Expression GetExpr<T>(T removable)
        {
            var assert = removable as AssertStmt;
            if (assert != null)
            {
                return assert.Expr;
            }
            var invariant = removable as MaybeFreeExpression;
            if (invariant != null)
            {
                return invariant.E;
            }
            return null;
        }

        private T GetNewNodeFromItem<T>(T brokenItem, BinaryExpr binExpr)
        {
            var assert = brokenItem as AssertStmt;
            if (assert != null)
            {
                return (T)(object)new AssertStmt(assert.Tok, assert.EndTok, binExpr, assert.Attributes);
            }
            var invariant = brokenItem as MaybeFreeExpression;
            if (invariant != null)
            {
                return (T)(object)new MaybeFreeExpression(binExpr);
            }
            return default(T);
        }

        private T GetNewNodeFromExpr<T>(T brokenItem, BinaryExpr binExpr, Expression subExpr)
        {
            var assert = brokenItem as AssertStmt;
            if (assert != null)
            {
                return (T)(object)new AssertStmt(binExpr.tok, assert.EndTok, subExpr, assert.Attributes);
            }
            var invariant = brokenItem as MaybeFreeExpression;
            if (invariant != null)
            {
                return (T)(object)new MaybeFreeExpression(binExpr);
            }
            return default(T);
        }

        private Tuple<T, T> SimplifyItem<T>(Wrap<T> wrap, int index)
        {
            var brokenItems = BreakAndReinsertItem(wrap, index);
            brokenItems.Reverse();
            //Test to see which can be removed
            for (var assertNum = brokenItems.Count - 1; assertNum >= 0; assertNum--)
            {
                var brokenItem = brokenItems[assertNum];
                if (!_remover.TryRemove(wrap)) continue;
                brokenItems.Remove(brokenItem);
            }
            return new Tuple<T, T>(wrap.Removable, CombineItems(brokenItems));
        }

        private List<T> BreakAndReinsertItem<T>(Wrap<T> wrap, int index)
        {
            var brokenAsserts = BreakDownExpr(wrap.Removable);
            foreach (var brokenAssert in brokenAsserts)
            {
                wrap.ParentList.Insert(index, brokenAssert);
            }
            return brokenAsserts;
        }

        private T CombineItems<T>(List<T> brokenItems)
        {
            if (brokenItems.Count < 1)
                return default(T); //null
            if (brokenItems.Count == 1)
                return brokenItems[0];

            var item = brokenItems[0];
            brokenItems.Remove(item);
            var left = GetExpr(brokenItems[0]);
            var right = GetExpr(CombineItems(brokenItems));
            var binExpr = new BinaryExpr(left.tok, BinaryExpr.Opcode.And, left, right);
            var newNode = GetNewNodeFromItem(brokenItems[0], binExpr);
            return newNode;
        }

        private List<T> BreakDownExpr<T>(T item)
        {
            var brokenItems = new List<T>();
            var binaryExpr = GetExpr(item) as BinaryExpr;
            if (binaryExpr == null || binaryExpr.Op != BinaryExpr.Opcode.And)
            {
                brokenItems.Add(item);
                return brokenItems;
            }
            var newItem1 = GetNewNodeFromExpr(item, binaryExpr, binaryExpr.E0);
            var newItem2 = GetNewNodeFromExpr(item, binaryExpr, binaryExpr.E1);
            brokenItems.AddRange(BreakDownExpr(newItem1));
            brokenItems.AddRange(BreakDownExpr(newItem2));
            return brokenItems;
        }

    }
}
