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
    class AllRemovableTypes
    {
        public readonly Dictionary<MemberDecl, RemovableTypesInMember> RemovableTypesInMethods = new Dictionary<MemberDecl, RemovableTypesInMember>();

        public ReadOnlyCollection<AssertWrap> Asserts {
            get {
                List<AssertWrap> asserts = new List<AssertWrap>();
                foreach (var removableTypes in RemovableTypesInMethods.Values)
                    asserts.AddRange(removableTypes.Asserts);
                return asserts.AsReadOnly();
            }
        }

        public ReadOnlyCollection<InvariantWrap> Invariants {
            get {
                List<InvariantWrap> invariants = new List<InvariantWrap>();
                foreach (var removableTypes in RemovableTypesInMethods.Values)
                    invariants.AddRange(removableTypes.Invariants);
                return invariants.AsReadOnly();
            }
        }

        public ReadOnlyCollection<DecreasesWrap> Decreases {
            get {
                List<DecreasesWrap> decreases = new List<DecreasesWrap>();
                foreach (var removableTypes in RemovableTypesInMethods.Values)
                    decreases.AddRange(removableTypes.Decreases);
                return decreases.AsReadOnly();
            }
        }

        public ReadOnlyCollection<WildCardDecreases> WildCardDecreaseses {
            get {
                List<WildCardDecreases> wildCardDecreases = new List<WildCardDecreases>();
                foreach (var removableTypes in RemovableTypesInMethods.Values)
                    wildCardDecreases.AddRange(removableTypes.WildCardDecreaseses);
                return wildCardDecreases.AsReadOnly();
            }
        }

        public ReadOnlyCollection<LemmaCallWrap> LemmaCalls {
            get {
                List<LemmaCallWrap> lemmaCalls = new List<LemmaCallWrap>();
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

        public void AddAssert(AssertWrap assert, MemberDecl member)
        {
            AddMember(member);
            RemovableTypesInMethods[member].Asserts.Add(assert);
        }

        public void AddInvariant(InvariantWrap invariant, MemberDecl member)
        {
            AddMember(member);
            RemovableTypesInMethods[member].Invariants.Add(invariant);
        }

        public void AddDecreases(DecreasesWrap decreases, MemberDecl member)
        {
            AddMember(member);
            RemovableTypesInMethods[member].Decreases.Add(decreases);
        }

        public void AddWildCardDecreases(WildCardDecreases wildCardDecreases, MemberDecl member)
        {
            AddMember(member);
            RemovableTypesInMethods[member].WildCardDecreaseses.Add(wildCardDecreases);
        }

        public void AddLemmaCall(LemmaCallWrap lemmaCall, MemberDecl member)
        {
            AddMember(member);
            RemovableTypesInMethods[member].LemmaCalls.Add(lemmaCall);
        }

        #endregion

        #region Removal Methods

        public void RemoveAssert(AssertWrap assertWrap)
        {
            foreach (var removableTypesInMethods in RemovableTypesInMethods) {
                if (!removableTypesInMethods.Value.Asserts.Contains(assertWrap)) continue;
                removableTypesInMethods.Value.Asserts.Remove(assertWrap);
                return;
            }
        }

        public void RemoveInvariant(InvariantWrap invariantWrap)
        {
            foreach (var removableTypesInMethods in RemovableTypesInMethods) {
                if (!removableTypesInMethods.Value.Invariants.Contains(invariantWrap)) continue;
                removableTypesInMethods.Value.Invariants.Remove(invariantWrap);
                return;
            }
        }

        public void RemoveDecreases(DecreasesWrap decreasesWrap)
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

        public void RemoveLemmaCall(LemmaCallWrap lemmaCall)
        {
            foreach (var removableTypesInMethods in RemovableTypesInMethods) {
                if (!removableTypesInMethods.Value.LemmaCalls.Contains(lemmaCall)) continue;
                removableTypesInMethods.Value.LemmaCalls.Remove(lemmaCall);
                return;
            }
        }

        #endregion
    }

    class RemovableTypesInMember
    {
        public MemberDecl Member { get; private set; }
        public readonly List<AssertWrap> Asserts = new List<AssertWrap>();
        public readonly List<InvariantWrap> Invariants = new List<InvariantWrap>();
        public readonly List<DecreasesWrap> Decreases = new List<DecreasesWrap>();
        public readonly List<WildCardDecreases> WildCardDecreaseses = new List<WildCardDecreases>();
        public readonly List<LemmaCallWrap> LemmaCalls = new List<LemmaCallWrap>();

        public RemovableTypesInMember(MemberDecl member)
        {
            Member = member;
        }
    }

    class Wrap<TRemovable,TParent>
    {
        public TRemovable Removeable { get; protected set; }
        public List<TParent> ParentList { get; private set; }
        
        public Wrap(TRemovable removable, List<TParent> parentList)
        {
            Removeable = removable;
            ParentList = parentList;
        }
    }

    class AssertWrap
    {
        public AssertStmt Assert { get; private set; }
        public List<Statement> ParentList { get; private set; }

        public AssertWrap(AssertStmt assert, List<Statement> parentList)
        {
            Assert = assert;
            ParentList = parentList;
        }
    }

    class InvariantWrap
    {
        public MaybeFreeExpression Invariant { get; private set; }
        public List<MaybeFreeExpression> ParentList { get; private set; }

        public InvariantWrap(MaybeFreeExpression invariant, List<MaybeFreeExpression> parentList)
        {
            Invariant = invariant;
            ParentList = parentList;
        }
    }

    class LemmaCallWrap
    {
        public UpdateStmt LemmaCall { get; private set; }
        public List<Statement> ParentList { get; private set; }

        public LemmaCallWrap(UpdateStmt lemmaCall, List<Statement> parentList)
        {
            LemmaCall = lemmaCall;
            ParentList = parentList;
        }
    }

    class DecreasesWrap
    {
        public Expression Decreases { get; private set; }
        public List<Expression> ParentList { get; private set; }

        public DecreasesWrap(Expression decreases, List<Expression> parentList)
        {
            Decreases = decreases;
            ParentList = parentList;
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


    internal class Shorty
    {
        public Program Program { get; private set; }

        // need to track methods relative to their class and module to check scopes for lemmaCalls

        private readonly AllRemovableTypes _allRemovableTypes;
        public ReadOnlyCollection<AssertWrap> Asserts { get { return _allRemovableTypes.Asserts; } }
        public ReadOnlyCollection<InvariantWrap> Invariants { get { return _allRemovableTypes.Invariants; } }
        public ReadOnlyCollection<DecreasesWrap> Decreases { get { return _allRemovableTypes.Decreases; } }
        public ReadOnlyCollection<WildCardDecreases> DecreasesWildCards { get { return _allRemovableTypes.WildCardDecreaseses; } }
        public ReadOnlyCollection<LemmaCallWrap> LemmaCalls { get { return _allRemovableTypes.LemmaCalls; } }

        #region Initialisation

        public Shorty(Program program)
        {
            Contract.Requires(program != null);
            Program = program;
            if (!IsProgramValid()) {
                throw new Exception("Initial program is not valid");
            }
            RemovalTypeFinder removalTypeFinder = new RemovalTypeFinder(program);
            _allRemovableTypes = removalTypeFinder.FindRemovables();
        }

        #endregion

        #region Utility

        public void PrintProgram(TextWriter writer)
        {
            Printer dafnyPrinter = new Printer(writer);
            dafnyPrinter.PrintProgram(Program, false);
        }

        #endregion

        #region Lemma Calls

        public List<UpdateStmt> FindRemovableLemmaCalls()
        {
            List<UpdateStmt> removableLemmaCalls = new List<UpdateStmt>();
            foreach (var lemmaCallWrap in _allRemovableTypes.LemmaCalls) {
                if (!TryRemoveLemmaCall(lemmaCallWrap)) continue;
                removableLemmaCalls.Add(lemmaCallWrap.LemmaCall);
            }
            return removableLemmaCalls;
        }

        private bool TryRemoveLemmaCall(LemmaCallWrap lemmaCallWrap)
        {
            var parentBody = lemmaCallWrap.ParentList;
            var lemmaCall = lemmaCallWrap.LemmaCall;
            var index = parentBody.IndexOf(lemmaCall);
            parentBody.Remove(lemmaCall);
            if (IsProgramValid()) {
                _allRemovableTypes.RemoveLemmaCall(lemmaCallWrap);
                return true;
            }
            parentBody.Insert(index, lemmaCall);
            return false;
        }

        #endregion

        #region decreases

        private bool TryRemoveDecreases(DecreasesWrap decreasesWrap)
        {
            var parent = decreasesWrap.ParentList;
            var decreases = decreasesWrap.Decreases;
            var position = parent.IndexOf(decreases);
            parent.Remove(decreases);
            if (IsProgramValid()) {
                _allRemovableTypes.RemoveDecreases(decreasesWrap);
                return true;
            }
            parent.Insert(position, decreases);
            return false;
        }

        public List<Expression> FindRemovableDecreases()
        {
            List<Expression> removableDecreases = new List<Expression>();
            foreach (DecreasesWrap decreasesWrap in _allRemovableTypes.Decreases) {
                if (!TryRemoveDecreases(decreasesWrap)) continue;
                removableDecreases.Add(decreasesWrap.Decreases);
            }
            //We also have to find removable wildcards which are stored differently
            removableDecreases.AddRange(FindRemovableWildCards());
            return removableDecreases;
        }

        private List<Expression> FindRemovableWildCards()
        {
            List<Expression> removableWildCards = new List<Expression>();
            foreach (var wcDecreases in _allRemovableTypes.WildCardDecreaseses)
                removableWildCards.AddRange(FindRemovableWildCards(wcDecreases).Item1);
            return removableWildCards;
        }

        private Tuple<List<Expression>, bool> FindRemovableWildCards(WildCardDecreases currentWildCardDecreases)
        {
            var removableWildCards = new List<Expression>();
            bool safeToRemove = true;
            RemoveWildCardSubDecreases(currentWildCardDecreases, removableWildCards, ref safeToRemove);

            if (safeToRemove)
                RemoveWildCardDecreases(currentWildCardDecreases, removableWildCards, ref safeToRemove);

            return new Tuple<List<Expression>, bool>(removableWildCards, safeToRemove);
        }

        private void RemoveWildCardDecreases(WildCardDecreases currentWildCardDecreases, List<Expression> removableWildCards, ref bool safeToRemove)
        {
            int index = currentWildCardDecreases.ParentSpecification.Expressions.IndexOf(currentWildCardDecreases.Expression);
            currentWildCardDecreases.ParentSpecification.Expressions.Remove(currentWildCardDecreases.Expression);
            if (IsProgramValid()) {
                removableWildCards.Add(currentWildCardDecreases.Expression);
                if(currentWildCardDecreases.ParentWildCardDecreases == null)
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
            List<MaybeFreeExpression> removableInvariants = new List<MaybeFreeExpression>();
            for (int i = _allRemovableTypes.Invariants.Count - 1; i >= 0; i--) {
                var invariantWrap = _allRemovableTypes.Invariants[i];
                if (!TryToRemoveInvariant(invariantWrap)) continue;
                removableInvariants.Add(invariantWrap.Invariant);
            }
            return removableInvariants;
        }

        private bool TryToRemoveInvariant(InvariantWrap invariantWrap)
        {
            var parent = invariantWrap.ParentList;
            var invariant = invariantWrap.Invariant;
            var position = parent.IndexOf(invariant);
            parent.Remove(invariant);
            if (IsProgramValid()) {
                _allRemovableTypes.RemoveInvariant(invariantWrap);
                return true;
            }
            parent.Insert(position, invariant);
            return false;
        }

        #endregion

        #region Asserts

        public Dictionary<Method, List<List<AssertStmt>>> TestDifferentRemovals()
        {
            Dictionary<Method, List<List<AssertStmt>>> returnData = new Dictionary<Method, List<List<AssertStmt>>>();
            foreach (Method method in _allRemovableTypes.RemovableTypesInMethods.Keys) {
                List<List<AssertStmt>> solutions = new List<List<AssertStmt>>();
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
            var assert = _allRemovableTypes.Asserts[index].Assert;
            var parent = _allRemovableTypes.Asserts[index].ParentList;
            TryRemovingAssertForOrderingTest(assert, parent, method, index, currentSolution, solutions);
        }

        private void TryRemovingAssertForOrderingTest(AssertStmt assert, List<Statement> parent, Method method, int index, List<AssertStmt> currentSolution, List<List<AssertStmt>> solutions)
        {
            int assertPos = parent.IndexOf(assert);
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
            foreach (AssertWrap assertWrap in _allRemovableTypes.Asserts) 
                TrySimplifyAssert(assertWrap, simplifiedAsserts);
            return simplifiedAsserts;
        }

        private void TrySimplifyAssert(AssertWrap assertWrap, List<Tuple<AssertStmt, AssertStmt>> simplifiedAsserts)
        {
            var assert = assertWrap.Assert;
            var parent = assertWrap.ParentList;
            var binExpr = assert.Expr as BinaryExpr;
            if (binExpr != null)
                if (binExpr.Op != BinaryExpr.Opcode.And) return;

            int index = parent.IndexOf(assert);
            parent.Remove(assert);
            if (!IsProgramValid()) {
                SimplifyAssert(assertWrap, index, simplifiedAsserts);
            }
            else {
                Console.WriteLine("Whole assert can be completely removed separately");
            }
        }

        private void SimplifyAssert(AssertWrap assertWrap, int index, List<Tuple<AssertStmt, AssertStmt>> simplifiedAsserts)
        {
            var brokenAsserts = BreakAndReinsertAssert(assertWrap.Assert, assertWrap.ParentList, index);
            brokenAsserts.Reverse();
            //Test to see which can be removed
            for (int assertNum = brokenAsserts.Count - 1; assertNum >= 0; assertNum--) {
                AssertStmt brokenAssert = brokenAsserts[assertNum];
                if (!TryRemoveAssert(assertWrap)) continue;
                brokenAsserts.Remove(brokenAssert);
            }
            simplifiedAsserts.Add(new Tuple<AssertStmt, AssertStmt>(assertWrap.Assert, CombineAsserts(brokenAsserts)));
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
            Expression left = brokenAsserts[0].Expr;
            Expression right = CombineAsserts(brokenAsserts).Expr;
            BinaryExpr binExpr = new BinaryExpr(left.tok, BinaryExpr.Opcode.And, left, right);
            AssertStmt newAssert = new AssertStmt(assert.Tok, assert.EndTok, binExpr, assert.Attributes);
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
            AssertStmt newAssert = new AssertStmt(binaryExpr.tok, assert.EndTok, binaryExpr.E0, assert.Attributes);
            AssertStmt newAssert2 = new AssertStmt(binaryExpr.tok, assert.EndTok, binaryExpr.E1, assert.Attributes);
            brokenAsserts.AddRange(BreakDownExpr(newAssert));
            brokenAsserts.AddRange(BreakDownExpr(newAssert2));
            return brokenAsserts;
        }

        public List<AssertStmt> FindRemovableAsserts()
        {
            List<AssertStmt> removedAsserts = new List<AssertStmt>();
            foreach (var assertWrap in _allRemovableTypes.Asserts) {
                if (!TryRemoveAssert(assertWrap)) continue;
                removedAsserts.Add(assertWrap.Assert);
            }
            return removedAsserts;
        }

        private bool TryRemoveAssert(AssertWrap assertWrap)
        {
            var parent = assertWrap.ParentList;
            var assert = assertWrap.Assert;
            int position = parent.IndexOf(assert);
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

        public void BoogieErrorInformation(Bpl.ErrorInformation errorInfo) {}

        private Program CloneProgram(Program program)
        {
            var cloner = new Cloner();
            var moduleDecl = new LiteralModuleDecl(cloner.CloneModuleDefinition(program.DefaultModuleDef, program.Name), null);
            return new Program(program.FullName, moduleDecl, program.BuiltIns, new ConsoleErrorReporter());
        }

        public bool IsProgramValid()
        {
            try {
                var programId = "main_program_id";
                var stats = new Bpl.PipelineStatistics();
                var translator = new Translator(new ConsoleErrorReporter());
                var programCopy = CloneProgram(Program);
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
                Console.WriteLine(!allOk ? "Verification failed" : "Verification Successful");
                return oc == Bpl.PipelineOutcome.VerificationCompleted && allOk;
            }
            catch {
                Console.WriteLine("Verification failed");
                return false;
            }
        }

        #endregion
    }

    class TestRemovalOrdering {}

    class RemovalTypeFinder
    {
        private Program Program { get; set; }
        AllRemovableTypes _allRemovableTypes = new AllRemovableTypes();
        private readonly Dictionary<ModuleDefinition, Dictionary<ClassDecl, List<Method>>> _allMethods = new Dictionary<ModuleDefinition, Dictionary<ClassDecl, List<Method>>>();


        public RemovalTypeFinder(Program program)
        {
            Program = program;
        }

        public AllRemovableTypes FindRemovables()
        {
            //First we need to find all the methods so the lemma calls can find them
            IdentifyModule(Program.DefaultModuleDef);
            //Now we check each module to find the removables
            FindRemovableTypesInModule(Program.DefaultModuleDef);
            return _allRemovableTypes;
        }

        private void IdentifyModule(ModuleDefinition module)
        {
            if (_allMethods.ContainsKey(module)) return;
            _allMethods.Add(module, new Dictionary<ClassDecl, List<Method>>());
            foreach (var decl in module.TopLevelDecls)
                IdentifyTopLevelDecl(decl);
        }

        private void IdentifyTopLevelDecl(Declaration decl)
        {
            if (decl is ClassDecl)
                IdentifyClass((ClassDecl)decl);
            else if (decl is LiteralModuleDecl)
            {
                LiteralModuleDecl literalModule = (LiteralModuleDecl)decl;
                IdentifyModule(literalModule.ModuleDef);
            }
        }

        private void IdentifyClass(ClassDecl classDecl)
        {
            _allMethods[classDecl.Module].Add(classDecl, new List<Method>());
            foreach (var member in classDecl.Members)
                if (member is Method)
                {
                    _allMethods[classDecl.Module][classDecl].Add((Method)member);
                    _allRemovableTypes.AddMember(member);
                }
        }

        private void FindRemovableTypesInModule(ModuleDefinition module)
        {
            foreach (var decl in module.TopLevelDecls)
            {
                if (decl is ClassDecl)
                    FindRemovableTypesInClass((ClassDecl)decl);
                else if (decl is LiteralModuleDecl)
                {
                    LiteralModuleDecl literalModule = (LiteralModuleDecl)decl;
                    FindRemovableTypesInModule(literalModule.ModuleDef);
                }
            }
        }

        private void FindRemovableTypesInClass(ClassDecl classDecl)
        {
            foreach (var member in classDecl.Members)
            {
                FindRemovableTypesInMember(member, classDecl);
            }
        }

        private void FindRemovableTypesInMember(MemberDecl member, ClassDecl classDecl)
        {
            WildCardDecreases wildCardParent = null; // The parent of the current wildCard we are tracking
            FindDecreasesTypesInMember(member, ref wildCardParent);
            var method = member as Method;
            if (method != null)
                FindRemovableTypesInMethod(method, wildCardParent, classDecl);
        }

        private void FindDecreasesTypesInMember(MemberDecl member, ref WildCardDecreases wildCardParent)
        {
            Specification<Expression> decreases = null;
            if (member is Method)
            {
                var method = (Method)member;
                decreases = method.Decreases;
            }
            else if (member is Function)
            {
                var function = (Function)member;
                decreases = function.Decreases;
            }
            if (decreases != null)
                FindDecreasesTypesInMethodFunction(decreases, ref wildCardParent, member);
        }

        private void FindDecreasesTypesInMethodFunction(Specification<Expression> decreases, ref WildCardDecreases wildCardParent, MemberDecl member)
        {
            foreach (var expression in decreases.Expressions)
            {
                if (expression is WildcardExpr)
                {
                    wildCardParent = new WildCardDecreases(expression, decreases, null);
                    _allRemovableTypes.AddWildCardDecreases(wildCardParent, (Method)member);
                    continue;
                }
                _allRemovableTypes.AddDecreases(new DecreasesWrap(expression, decreases.Expressions), member);
            }
        }

        private void FindRemovableTypesInMethod(Method method, WildCardDecreases wildCardParent, ClassDecl classDecl)
        {
            if (method.Body == null) return;
            var block = method.Body;
            foreach (var statement in block.Body)
                FindRemovableTypesInStatement(statement, block, method, wildCardParent, classDecl);
        }

        private void FindRemovableTypesInStatement(Statement statement, Statement parent, Method method, WildCardDecreases wildCardParent, ClassDecl classDecl)
        {
            if (statement is AssertStmt)
                FindRemovableTypesInAssertStmt((AssertStmt)statement, parent, method);
            else if (statement is BlockStmt)
                FindRemovableTypesInBlockStmt((BlockStmt)statement, method, wildCardParent, classDecl);
            else if (statement is IfStmt)
                FindRemovableTypesInIfStmt((IfStmt)statement, method, wildCardParent, classDecl);
            else if (statement is LoopStmt)
                FindRemovableTypesInLoopStmt((LoopStmt)statement, method, wildCardParent, classDecl);
            else if (statement is MatchStmt)
                FindRemovableTypesInMatchStmt((MatchStmt)statement, method, wildCardParent, classDecl);
            else if (statement is ForallStmt)
                FindRemovableTypesInForallStmt((ForallStmt)statement, method, wildCardParent, classDecl);
            else if (statement is CalcStmt)
                FindRemovableTypesInCalcStmt((CalcStmt)statement, method, wildCardParent, classDecl);
            else if (statement is UpdateStmt)
                FindRemovableTypesInUpdateStmt((UpdateStmt)statement, parent, method, classDecl);
        }

        private void FindRemovableTypesInCalcStmt(CalcStmt calc, Method method, WildCardDecreases wildCardParent, ClassDecl classDecl)
        {
            foreach (var hint in calc.Hints)
                FindRemovableTypesInStatement(hint, calc, method, wildCardParent, classDecl);
        }

        private void FindRemovableTypesInForallStmt(ForallStmt forall, Method method, WildCardDecreases wildCardParent, ClassDecl classDecl)
        {
            FindRemovableTypesInStatement(forall.Body, forall, method, wildCardParent, classDecl);
        }

        private void FindRemovableTypesInMatchStmt(MatchStmt match, Method method, WildCardDecreases wildCardParent, ClassDecl classDecl)
        {
            foreach (MatchCaseStmt matchCase in match.Cases)
                foreach (Statement stmt in matchCase.Body)
                    FindRemovableTypesInStatement(stmt, match, method, wildCardParent, classDecl);
        }

        private void FindRemovableTypesInLoopStmt(LoopStmt loopStmt, Method method, WildCardDecreases wildCardParent, ClassDecl classDecl)
        {
            GetLoopInvariants(loopStmt, method);
            IdentifyRemovableDecreasesTypesInLoop(loopStmt, method, ref wildCardParent);
            if (!(loopStmt is WhileStmt)) return;
            WhileStmt whileStmt = (WhileStmt)loopStmt;
            FindRemovableTypesInStatement(whileStmt.Body, loopStmt, method, wildCardParent, classDecl);
        }

        private void IdentifyRemovableDecreasesTypesInLoop(LoopStmt loop, Method method, ref WildCardDecreases wildCardParent)
        {
            //Deal with wildcard decreases
            foreach (Expression expr in loop.Decreases.Expressions)
            {
                IdentifyDecreasesExpression(loop, method, ref wildCardParent, expr);
            }
        }

        private void IdentifyDecreasesExpression(LoopStmt loop, Method method, ref WildCardDecreases wildCardParent, Expression expr)
        {
            if (expr is WildcardExpr)
                IdentifyWildCardDecreases(loop, ref wildCardParent, expr);
            else
                _allRemovableTypes.AddDecreases(new DecreasesWrap(expr, loop.Decreases.Expressions), method);
        }

        private void IdentifyWildCardDecreases(LoopStmt loop, ref WildCardDecreases wildCardParent, Expression expr)
        {
            var newWildCard = new WildCardDecreases(expr, loop.Decreases, wildCardParent);
            wildCardParent.SubDecreases.Add(newWildCard);
            wildCardParent = newWildCard;
        }

        void GetLoopInvariants(LoopStmt loop, Method method)
        {
            //Invariants.Add(loop, loop.Invariants);
            foreach (var invariant in loop.Invariants)
            {
                _allRemovableTypes.AddInvariant(new InvariantWrap(invariant, loop.Invariants), method);
            }
        }

        private void FindRemovableTypesInIfStmt(IfStmt ifstmt, Method method, WildCardDecreases wildCardParent, ClassDecl classDecl)
        {
            FindRemovableTypesInStatement(ifstmt.Thn, ifstmt, method, wildCardParent, classDecl);
            FindRemovableTypesInStatement(ifstmt.Els, ifstmt, method, wildCardParent, classDecl);
        }

        private void FindRemovableTypesInBlockStmt(BlockStmt blockStmt, Method method, WildCardDecreases wildCardParent, ClassDecl classDecl)
        {
            foreach (var stmt in blockStmt.Body)
                FindRemovableTypesInStatement(stmt, blockStmt, method, wildCardParent, classDecl);
        }

        private void FindRemovableTypesInAssertStmt(AssertStmt assert, Statement parent, Method method)
        {
            if (!(parent is BlockStmt)) return;
            BlockStmt block = (BlockStmt)parent;
            AssertWrap assertWrap = new AssertWrap(assert, block.Body);
            _allRemovableTypes.AddAssert(assertWrap, method);
        }

        private void FindRemovableTypesInUpdateStmt(UpdateStmt updateStmt, List<Statement> parent, Method method, ClassDecl classDecl)
        {
            foreach (var expr in updateStmt.Rhss)
            {
                if (!IsAssignmentLemmaCall(expr, classDecl)) continue;
                _allRemovableTypes.AddLemmaCall(new LemmaCallWrap(updateStmt, parent), method);
            }
        }

        private void FindRemovableTypesInUpdateStmt(UpdateStmt updateStmt, Statement parent, Method method, ClassDecl classDecl)
        {
            if (parent is BlockStmt)
            {
                var blockStmt = (BlockStmt)parent;
                FindRemovableTypesInUpdateStmt(updateStmt, blockStmt.Body, method, classDecl);
            }
            else if (parent is MatchStmt)
            {
                var matchStmt = (MatchStmt)parent;
                foreach (var matchCase in matchStmt.Cases)
                {
                    if (!matchCase.Body.Contains(updateStmt)) continue;
                    FindRemovableTypesInUpdateStmt(updateStmt, matchCase.Body, method, classDecl);
                    break;
                }
            }
        }

        private bool IsAssignmentLemmaCall(AssignmentRhs expr, ClassDecl classDecl)
        {
            var exprRhs = expr as ExprRhs;
            if (exprRhs == null) return false;
            if (!(exprRhs.Expr is ApplySuffix)) return false;
            return IsCallToGhost((ApplySuffix)exprRhs.Expr, classDecl);
        }

        private bool IsCallToGhost(SuffixExpr expr, ClassDecl classDecl)
        {
            var name = "";
            var nameSeg = expr.Lhs as NameSegment;
            if (nameSeg != null)
                name = nameSeg.Name;

            // Look through all the methods within the current scope and return whether it is ghost or not
            return (from method in _allMethods[classDecl.Module][classDecl] where method.Name == name select method.IsGhost).FirstOrDefault();
        }

    }

    class Remover
    {
        
    }
}
