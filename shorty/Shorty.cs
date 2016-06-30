using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;
using Microsoft.Dafny;
using Bpl = Microsoft.Boogie;

namespace shorty
{
    class RemovableItemsInMethod
    {
        public Method Method { get; private set; }
        public List<AssertWrap> Asserts = new List<AssertWrap>();

        public RemovableItemsInMethod(Method method)
        {
            Method = method;
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
        public List<UpdateStmt> ParentList { get; private set; }

        public LemmaCallWrap(UpdateStmt lemmaCall, List<UpdateStmt> parentList)
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


    internal class Shorty
    {
        public Program Program { get; private set; }

        public Dictionary<Method, RemovableItemsInMethod> RemoveableItemsInMethods = new Dictionary<Method, RemovableItemsInMethod>();

        private readonly List<AssertWrap> _asserts = new List<AssertWrap>();
        public List<AssertWrap> Asserts { get { return _asserts; } }

        private readonly List<InvariantWrap> _invariants = new List<InvariantWrap>();
        public List<InvariantWrap> Invariants {get {return _invariants; } }

        private readonly  List<DecreasesWrap> _decreases = new List<DecreasesWrap>();
        public List<DecreasesWrap> Decreases {get { return _decreases; } }
        public readonly List<WildCardDecreases> DecreasesWildCards = new List<WildCardDecreases>();

        // Need to create a tree to keep track of wild card decreases so we know who the parent of each one is as we need to remove bottom up
        internal class WildCardDecreases
        {
            public readonly Expression Expression;
            public readonly Specification<Expression> ParentSpecification;
            public readonly WildCardDecreases ParentWildCardDecreases;
            public readonly List<WildCardDecreases> SubDecreases = new List<WildCardDecreases>();

            public int Count {
                get {
                    return 1 + SubDecreases.Sum(wildCardDecreases => wildCardDecreases.Count);
                }
            }

            public WildCardDecreases(Expression decreasesExpression, Specification<Expression> parentSpecification, WildCardDecreases parentWildCardDecreases)
            {
                Expression = decreasesExpression;
                ParentSpecification = parentSpecification;
                ParentWildCardDecreases = parentWildCardDecreases;
            }
        }


        //Lemma Calls
        //Need to keep track of methods and scope
        private readonly Dictionary<ModuleDefinition, Dictionary<ClassDecl, List<Method>>> _allMethods = new Dictionary<ModuleDefinition, Dictionary<ClassDecl, List<Method>>>();
        private readonly Dictionary<Statement, List<UpdateStmt>> _lemmaCalls = new Dictionary<Statement, List<UpdateStmt>>(); //The type of lemma calls we want to remove are inside UpdateStatement

        public Dictionary<Statement, List<UpdateStmt>> LemmaCalls {
            get { return _lemmaCalls; }
        }

        #region Initialisation

        public Shorty(Program program)
        {
            Contract.Requires(program != null);
            Program = program;
            if (!IsProgramValid()) {
                throw new Exception("Initial program is not valid");
            }
            FindRemovables();
        }

        #endregion

        #region Utility

        public void PrintProgram(TextWriter writer)
        {
            Printer dafnyPrinter = new Printer(writer);
            dafnyPrinter.PrintProgram(Program, false);
        }

        #endregion

        #region tree traversal

        private void FindRemovables()
        {
            //First we need to find all the methods so the lemma calls can find them
            IdentifyModule(Program.DefaultModuleDef);
            //Now we check each module to find the removables
            FindRemovableTypesInModule(Program.DefaultModuleDef);
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
                IdentifyClass((ClassDecl) decl);
            else if (decl is LiteralModuleDecl) {
                LiteralModuleDecl literalModule = (LiteralModuleDecl) decl;
                IdentifyModule(literalModule.ModuleDef);
            }
        }

        private void IdentifyClass(ClassDecl classDecl)
        {
            _allMethods[classDecl.Module].Add(classDecl, new List<Method>());
            foreach (var member in classDecl.Members)
                if (member is Method) {
                    _allMethods[classDecl.Module][classDecl].Add((Method) member);
                    RemoveableItemsInMethods.Add((Method) member, new RemovableItemsInMethod((Method) member));
                }
        }

        private void FindRemovableTypesInModule(ModuleDefinition module)
        {
            foreach (var decl in module.TopLevelDecls) {
                if (decl is ClassDecl)
                    FindRemovableTypesInClass((ClassDecl) decl);
                else if (decl is LiteralModuleDecl) {
                    LiteralModuleDecl literalModule = (LiteralModuleDecl) decl;
                    FindRemovableTypesInModule(literalModule.ModuleDef);
                }
            }
        }

        private void FindRemovableTypesInClass(ClassDecl classDecl)
        {
            foreach (var member in classDecl.Members) {
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
            if (member is Method) {
                var method = (Method) member;
                decreases = method.Decreases;
            }
            else if (member is Function) {
                var function = (Function) member;
                decreases = function.Decreases;
            }
            if (decreases != null)
                FindDecreasesTypesInMethodFunction(decreases, ref wildCardParent, member);
        }

        private void FindDecreasesTypesInMethodFunction(Specification<Expression> decreases, ref WildCardDecreases wildCardParent, MemberDecl member)
        {
            foreach (var expression in decreases.Expressions) {
                if (expression is WildcardExpr) {
                    wildCardParent = new WildCardDecreases(expression, decreases, null);
                    DecreasesWildCards.Add(wildCardParent);
                    continue;
                }
                Decreases.Add(new DecreasesWrap(expression, decreases.Expressions));
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
                FindRemovableTypesInAssertStmt((AssertStmt) statement, parent, method);
            else if (statement is BlockStmt)
                FindRemovableTypesInBlockStmt((BlockStmt) statement, method, wildCardParent, classDecl);
            else if (statement is IfStmt)
                FindRemovableTypesInIfStmt((IfStmt) statement, method, wildCardParent, classDecl);
            else if (statement is LoopStmt)
                FindRemovableTypesInLoopStmt((LoopStmt) statement, method, wildCardParent, classDecl);
            else if (statement is MatchStmt)
                FindRemovableTypesInMatchStmt((MatchStmt) statement, method, wildCardParent, classDecl);
            else if (statement is ForallStmt)
                FindRemovableTypesInForallStmt((ForallStmt) statement, method, wildCardParent, classDecl);
            else if (statement is CalcStmt)
                FindRemovableTypesInCalcStmt((CalcStmt) statement, method, wildCardParent, classDecl);
            else if (statement is UpdateStmt)
                FindRemovableTypesInUpdateStmt((UpdateStmt) statement, parent, classDecl);
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
            GetLoopInvariants(loopStmt);
            IdentifyRemovableDecreasesTypesInLoop(loopStmt, method, ref wildCardParent);
            if (!(loopStmt is WhileStmt)) return;
            WhileStmt whileStmt = (WhileStmt) loopStmt;
            FindRemovableTypesInStatement(whileStmt.Body, loopStmt, method, wildCardParent, classDecl);
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
//            if (!_asserts.ContainsKey(method))
//                _asserts.Add(method, new Dictionary<Statement, List<AssertStmt>>());
//            if (!Asserts[method].ContainsKey(parent))
//                _asserts[method].Add(parent, new List<AssertStmt>());
//            if (!_asserts[method][parent].Contains(assert))
//                _asserts[method][parent].Add(assert);

            if (parent is BlockStmt) {
                BlockStmt block = (BlockStmt) parent;
                AssertWrap assertWrap = new AssertWrap(assert, block.Body);
                Asserts.Add(assertWrap);
                RemoveableItemsInMethods[method].Asserts.Add(assertWrap);
            }
        }

        private void FindRemovableTypesInUpdateStmt(UpdateStmt updateStmt, Statement parent, ClassDecl classDecl)
        {
            foreach (var expr in updateStmt.Rhss) {
                if (!IsAssignmentLemmaCall(expr, classDecl)) continue;
                if (!_lemmaCalls.ContainsKey(parent))
                    _lemmaCalls.Add(parent, new List<UpdateStmt>());
                _lemmaCalls[parent].Add(updateStmt);
            }
        }

        private bool IsAssignmentLemmaCall(AssignmentRhs expr, ClassDecl classDecl)
        {
            var exprRhs = expr as ExprRhs;
            if (exprRhs == null) return false;
            if (!(exprRhs.Expr is ApplySuffix)) return false;
            return IsCallToGhost((ApplySuffix) exprRhs.Expr, classDecl);
        }

        #endregion

        #region Lemma Calls

        private bool IsCallToGhost(SuffixExpr expr, ClassDecl classDecl)
        {
            var name = "";
            var nameSeg = expr.Lhs as NameSegment;
            if (nameSeg != null)
                name = nameSeg.Name;

            // Look through all the methods within the current scope and return whether it is ghost or not
            return (from method in _allMethods[classDecl.Module][classDecl] where method.Name == name select method.IsGhost).FirstOrDefault();
        }


        public List<UpdateStmt> FindRemovableLemmaCalls()
        {
            List<UpdateStmt> removableLemmaCalls = new List<UpdateStmt>();
            foreach (var stmt in _lemmaCalls.Keys) {
                var blockStmt = stmt as BlockStmt;
                if (blockStmt != null)
                    FindRemovableLemmaCallsInBlock(blockStmt, removableLemmaCalls);
                else if (stmt is MatchStmt) {}
                //TODO: Somethign about match cases for lemma calls
            }
            return removableLemmaCalls;
        }

        private void FindRemovableLemmaCallsInBlock(BlockStmt blockStmt, List<UpdateStmt> removableLemmaCalls)
        {
            foreach (var lemmaCall in LemmaCalls[blockStmt])
                TryRemoveLemmaCall(blockStmt.Body, lemmaCall, removableLemmaCalls);
        }

        private void TryRemoveLemmaCall(List<Statement> parentBody, UpdateStmt lemmaCall, List<UpdateStmt> removableLemmaCalls)
        {
            var index = parentBody.IndexOf(lemmaCall);
            parentBody.Remove(lemmaCall);
            if (!IsProgramValid())
                parentBody.Insert(index, lemmaCall);
            else
                removableLemmaCalls.Add(lemmaCall);
        }

        #endregion

        #region decreases

        private void IdentifyRemovableDecreasesTypesInLoop(LoopStmt loop, Method method, ref WildCardDecreases wildCardParent)
        {
            //Deal with wildcard decreases
            foreach (Expression expr in loop.Decreases.Expressions) {
                IdentifyDecreasesExpression(loop, method, ref wildCardParent, expr);
            }
        }

        private void IdentifyDecreasesExpression(LoopStmt loop, Method method, ref WildCardDecreases wildCardParent, Expression expr)
        {
            if (expr is WildcardExpr)
                IdentifyWildCardDecreases(loop, ref wildCardParent, expr);
            else
                Decreases.Add(new DecreasesWrap(expr, loop.Decreases.Expressions));
        }

        private void IdentifyWildCardDecreases(LoopStmt loop, ref WildCardDecreases wildCardParent, Expression expr)
        {
            var newWildCard = new WildCardDecreases(expr, loop.Decreases, wildCardParent);
            if (wildCardParent != null)
                wildCardParent.SubDecreases.Add(newWildCard);
            else
                DecreasesWildCards.Add(newWildCard); // There is no parent - add new one
            wildCardParent = newWildCard;
        }

        private bool TryRemoveDecreases(Expression decreases, List<Expression> parent)
        {
            var position = parent.IndexOf(decreases);
            if (decreases == null || decreases is WildcardExpr) return false;
            parent.Remove(decreases);
            if (IsProgramValid()) return true;
            parent.Insert(position, decreases);
            return false;
        }

        public List<Expression> FindRemoveableDecreases()
        {
            List<Expression> removeableDecreases = new List<Expression>();
            foreach (DecreasesWrap decreasesWrap in Decreases) {
                if(!TryRemoveDecreases(decreasesWrap.Decreases, decreasesWrap.ParentList)) continue;
                removeableDecreases.Add(decreasesWrap.Decreases);
            }
            //We also have to find removable wildcards which are stored differently
            removeableDecreases.AddRange(FindRemovableWildCards());
            return removeableDecreases;
        }

        private List<Expression> FindRemovableWildCards()
        {
            List<Expression> removableWildCards = new List<Expression>();
            foreach (var wcDecreases in DecreasesWildCards)
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
            if (IsProgramValid())
                removableWildCards.Add(currentWildCardDecreases.Expression);
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

        void GetLoopInvariants(LoopStmt loop)
        {
            //Invariants.Add(loop, loop.Invariants);
            foreach (var invariant in loop.Invariants) {
                Invariants.Add(new InvariantWrap(invariant, loop.Invariants));
            }
        }

        public List<MaybeFreeExpression> FindRemovableInvariants()
        {
            List<MaybeFreeExpression> removeableInvariants = new List<MaybeFreeExpression>();
            for (int i = Invariants.Count - 1; i >= 0; i--) {
                var invariant = Invariants[i].Invariant;
                if(!TryToRemoveInvariant(invariant, Invariants[i].ParentList)) continue;
                removeableInvariants.Add(invariant);
            }
            return removeableInvariants;
        }

        private bool TryToRemoveInvariant(MaybeFreeExpression invariant, List<MaybeFreeExpression> parent)
        {
            int position = parent.IndexOf(invariant);
            parent.Remove(invariant);
            if (IsProgramValid()) 
                return true;
            parent.Insert(position, invariant);
            return false;
        }

        #endregion

        #region Asserts

        public Dictionary<Method, List<List<AssertStmt>>> TestDifferentRemovals()
        {
            Dictionary<Method, List<List<AssertStmt>>> returnData = new Dictionary<Method, List<List<AssertStmt>>>();
            foreach (Method method in RemoveableItemsInMethods.Keys) {
                List<List<AssertStmt>> solutions = new List<List<AssertStmt>>();
                TestAssertRemovalOrdering(0, solutions, new List<AssertStmt>(), method);
                returnData.Add(method, solutions);
            }
            return returnData;
        }

        private void TestAssertRemovalOrdering(int index, List<List<AssertStmt>> solutions, List<AssertStmt> currentSolution, Method method)
        {
            if (index == RemoveableItemsInMethods[method].Asserts.Count) {
                solutions.Add(new List<AssertStmt>(currentSolution));
                return;
            }
            var assert = Asserts[index].Assert;
            var parent = Asserts[index].ParentList;
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

            foreach (AssertWrap assertWrap in Asserts) {
                var assert = assertWrap.Assert;
                var parent = assertWrap.ParentList;
                //Check and see if it is an AND operation - if not, continue
                TrySimplifyAssert(assert, parent, simplifiedAsserts);
            }

            return simplifiedAsserts;
        }

        private void TrySimplifyAssert(AssertStmt assert, List<Statement> parent, List<Tuple<AssertStmt, AssertStmt>> simplifiedAsserts)
        {
            var binExpr = assert.Expr as BinaryExpr;
            if (binExpr != null)
                if (binExpr.Op != BinaryExpr.Opcode.And) return;

            int index = parent.IndexOf(assert);
            parent.Remove(assert);
            if (!IsProgramValid()) {
                SimplifyAssert(assert, parent, index, simplifiedAsserts);
            }
            else {
                Console.WriteLine("Whole assert can be completely removed separately");
            }
        }

        private void SimplifyAssert(AssertStmt assert, List<Statement> parent, int index, List<Tuple<AssertStmt, AssertStmt>> simplifiedAsserts)
        {
            var brokenAsserts = BreakAndReinsertAssert(assert, parent, index);
            brokenAsserts.Reverse();
            //Test to see which can be removed
            for (int assertNum = brokenAsserts.Count - 1; assertNum >= 0; assertNum--) {
                AssertStmt brokenAssert = brokenAsserts[assertNum];
                if (!TryRemoveAssert(parent, brokenAssert)) continue;
                brokenAsserts.Remove(brokenAssert);
            }
            simplifiedAsserts.Add(new Tuple<AssertStmt, AssertStmt>(assert, CombineAsserts(brokenAsserts)));
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
            foreach (var assertWrap in Asserts) {
                if (!TryRemoveAssert(assertWrap.ParentList, assertWrap.Assert)) continue;
                removedAsserts.Add(assertWrap.Assert);
            }
            return removedAsserts;
        }

        private bool TryRemoveAssert(List<Statement> parent, AssertStmt assert)
        {
            int position = parent.IndexOf(assert);
            parent.Remove(assert);
            if (IsProgramValid()) return true;
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
}
