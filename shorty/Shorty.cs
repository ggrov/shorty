using System;
using System.Collections.Generic;
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

        //Asserts
        private readonly Dictionary<Method, Dictionary<Statement, List<AssertStmt>>> _asserts = new Dictionary<Method, Dictionary<Statement, List<AssertStmt>>>();

        public Dictionary<Method, Dictionary<Statement, List<AssertStmt>>> Asserts {
            get { return _asserts; }
        }

        //Invariants
        private readonly Dictionary<LoopStmt, List<MaybeFreeExpression>> _invariants = new Dictionary<LoopStmt, List<MaybeFreeExpression>>();

        public Dictionary<LoopStmt, List<MaybeFreeExpression>> Invariants {
            get { return _invariants; }
        }

        //Decreases - method<(methodDecreases, loops<loopDecreases>)>
        private readonly Dictionary<MemberDecl, Tuple<List<Expression>, Dictionary<LoopStmt, List<Expression>>>> _decreases = new Dictionary<MemberDecl, Tuple<List<Expression>, Dictionary<LoopStmt, List<Expression>>>>();

        public Dictionary<MemberDecl, Tuple<List<Expression>, Dictionary<LoopStmt, List<Expression>>>> Decreases {
            get { return _decreases; }
        }
        public readonly List<WildCardDecreases> wildCardDecreases = new List<WildCardDecreases>();

        // Need to create a tree to keep track of wild card decreases so we know who the parent of each one is as we need to remove bottom up
        internal class WildCardDecreases
        {
            public readonly Expression Expression;
            public readonly Specification<Expression> ParentSpecification;
            public readonly WildCardDecreases ParentWildCardDecreases;
            public readonly List<WildCardDecreases> SubDecreases = new List<WildCardDecreases>();

            public int Count()
            {
                int count = 1;
                foreach (var wildCardDecreases in SubDecreases) {
                    count += wildCardDecreases.Count();
                }
                return count;
            }

            public WildCardDecreases(Expression decreasesExpression, Specification<Expression> parentSpecification, WildCardDecreases parentWildCardDecreases)
            {
                Expression = decreasesExpression;
                ParentSpecification = parentSpecification;
                ParentWildCardDecreases = parentWildCardDecreases;
            }
        }


        //Lemma Calls
        //Need to keep track of methods
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
            FindRemovables();
        }

        public void PrintAsserts()
        {
            Console.WriteLine();
            int i = 0, j = 0;

            foreach (var method in _asserts.Keys) {
                Console.WriteLine("Method " + method.Name);
                foreach (var block in _asserts[method].Keys) {
                    Console.WriteLine("Block " + ++i + ", Line " + block.Tok.line);
                    foreach (var assert in _asserts[method][block]) {
                        Console.WriteLine(++j + ": " + assert.Tok.line);
                    }
                }
            }
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
                IdentifyClass((ClassDecl)decl);
            else if (decl is LiteralModuleDecl){
                LiteralModuleDecl literalModule = (LiteralModuleDecl)decl;
                IdentifyModule(literalModule.ModuleDef);
            }
        }

        private void IdentifyClass(ClassDecl classDecl)
        {
            _allMethods[classDecl.Module].Add(classDecl, new List<Method>());
            foreach (var member in classDecl.Members)
                if (member is Method)
                    _allMethods[classDecl.Module][classDecl].Add((Method)member);
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

        private void FindDecreasesTypesInMethodFunction(Specification<Expression> decreases, ref WildCardDecreases wildCardParent, MemberDecl member )
        {
            foreach (var expression in decreases.Expressions) {
                if (expression is WildcardExpr) {
                    wildCardParent = new WildCardDecreases(expression, decreases, null);
                    wildCardDecreases.Add(wildCardParent);
                    continue;
                }
                if (!_decreases.ContainsKey(member)) 
                    _decreases.Add(member, new Tuple<List<Expression>, Dictionary<LoopStmt, List<Expression>>>(new List<Expression>(), new Dictionary<LoopStmt, List<Expression>>()));
                _decreases[member].Item1.Add(expression);
            }
        }

        private void FindRemovableTypesInMethod(Method method, WildCardDecreases wildCardParent, ClassDecl classDecl)
        {
            if(method.Body == null) return;
            var block = method.Body;
            foreach (var statement in block.Body)
                FindRemovableTypesInStatement(statement, block, method, wildCardParent, classDecl);
        }

        private void FindRemovableTypesInStatement(Statement statement, Statement parent, Method method, WildCardDecreases wildCardParent, ClassDecl classDecl)
        {
            if (statement is AssertStmt)
                FindRemovableTypesInAssertStmt((AssertStmt) statement, parent, method);
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

        private void FindRemovableTypesInLoopStmt(LoopStmt loopStmt, Method method,  WildCardDecreases wildCardParent, ClassDecl classDecl)
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
            if (!_asserts.ContainsKey(method))
                _asserts.Add(method, new Dictionary<Statement, List<AssertStmt>>());
            if (!Asserts[method].ContainsKey(parent))
                _asserts[method].Add(parent, new List<AssertStmt>());
            if (!_asserts[method][parent].Contains(assert))
                _asserts[method][parent].Add(assert);
        }

        private void FindRemovableTypesInUpdateStmt(UpdateStmt updateStmt, Statement parent, ClassDecl classDecl)
        {
            foreach (var expr in updateStmt.Rhss) {
                if(!IsAssignmentLemmaCall(expr, classDecl)) continue;
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
            return IsCallToGhost((ApplySuffix)exprRhs.Expr, classDecl);
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

        private void TryRemoveLemmaCall(List<Statement> parentBody,  UpdateStmt lemmaCall, List<UpdateStmt>removableLemmaCalls)
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
                IdentifyNormalDecreases(loop, method, expr);
        }

        private void IdentifyNormalDecreases(LoopStmt loop, Method method, Expression expr)
        {
            if (!_decreases.ContainsKey(method))
                _decreases.Add(method, new Tuple<List<Expression>, Dictionary<LoopStmt, List<Expression>>>(new List<Expression>(), new Dictionary<LoopStmt, List<Expression>>()));
            if (!_decreases[method].Item2.ContainsKey(loop))
                _decreases[method].Item2.Add(loop, new List<Expression>());
            _decreases[method].Item2[loop].Add(expr);
        }

        private void IdentifyWildCardDecreases(LoopStmt loop, ref WildCardDecreases wildCardParent, Expression expr)
        {
            var newWildCard = new WildCardDecreases(expr, loop.Decreases, wildCardParent);
            if (wildCardParent != null)
                wildCardParent.SubDecreases.Add(newWildCard);
            else
                wildCardDecreases.Add(newWildCard); // There is no parent - add new one
            wildCardParent = newWildCard;
        }

        public List<Expression> RemoveDecreasesFromParent(List<Expression> decreases)
        {
            List<Expression> removeableDecreases = new List<Expression>();

            for (int i = decreases.Count - 1; i >= 0; i--) {
                RemoveSingleDecreasesFromParent(decreases, i, removeableDecreases);
            }

            return removeableDecreases;
        }

        private void RemoveSingleDecreasesFromParent(List<Expression> decreases, int position, List<Expression> removeableDecreases)
        {
            var expr = decreases[position];
            if (expr == null || expr is WildcardExpr) return;
            decreases.RemoveAt(position);
            if (!IsProgramValid()) 
                decreases.Insert(position, expr);
            else 
                removeableDecreases.Add(expr);
        }

        public List<Expression> FindRemoveableDecreases()
        {
            List<Expression> removeableDecreases = new List<Expression>();
            foreach (MemberDecl member in _decreases.Keys) {
                FindRemovableDecreasesInMember(member, removeableDecreases);
                FindRemovableDecreasesInMembersLoops(member, removeableDecreases);
            }
            //We also have to find removable wildcards which are stored differently
            removeableDecreases.AddRange(FindRemovableWildCards()); 
            return removeableDecreases;
        }

        private void FindRemovableDecreasesInMembersLoops(MemberDecl member, List<Expression> removeableDecreases)
        {
            foreach (var loop in _decreases[member].Item2.Keys) 
                removeableDecreases.AddRange(RemoveDecreasesFromParent(loop.Decreases.Expressions));
        }

        private void FindRemovableDecreasesInMember(MemberDecl member, List<Expression> removeableDecreases)
        {
            if (member is Method) {
                var method = (Method) member;
                removeableDecreases.AddRange(RemoveDecreasesFromParent(method.Decreases.Expressions));
            }
            else if (member is Function) {
                var function = (Function) member;
                removeableDecreases.AddRange(RemoveDecreasesFromParent(function.Decreases.Expressions));
            }
        }

        private List<Expression> FindRemovableWildCards()
        {
            List<Expression> removableWildCards = new List<Expression>();
            foreach (var wcDecreases in wildCardDecreases)
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
            if (!_invariants.ContainsKey(loop))
                _invariants.Add(loop, loop.Invariants);
        }

        public List<MaybeFreeExpression> FindRemovableInvariants()
        {
            List<MaybeFreeExpression> removeableInvariants = new List<MaybeFreeExpression>();
            foreach (var loopStmt in _invariants.Keys) 
                FindRemoveableInvariantsInLoop(_invariants[loopStmt], removeableInvariants);
            return removeableInvariants;
        }

        private void FindRemoveableInvariantsInLoop(List<MaybeFreeExpression> invariantList, List<MaybeFreeExpression> removeableInvariants)
        {
            for (int i = invariantList.Count - 1; i >= 0; i--) 
                TryToRemoveInvariant(invariantList, removeableInvariants, i);
        }

        private void TryToRemoveInvariant(List<MaybeFreeExpression> invariantList, List<MaybeFreeExpression> removeableInvariants, int position)
        {
            MaybeFreeExpression invariant = invariantList[position];
            invariantList.Remove(invariant);
            if (!IsProgramValid())
                invariantList.Insert(position, invariant);
            else
                removeableInvariants.Add(invariant);
        }

        #endregion

        #region Asserts

        private AssertStmt GetAssertByIndex(int index, Method method)
        {
            int count = 0;
            foreach (var block in _asserts[method].Keys) {
                if (count + _asserts[method][block].Count - 1 < index) 
                    count += _asserts[method][block].Count - 1;
                else 
                    return _asserts[method][block][index - count];
            }
            return null;
        }

        private Statement GetParentByIndex(int index, Method method)
        {
            int count = 0;
            foreach (var block in _asserts[method].Keys) {
                if (count + _asserts[method][block].Count - 1 < index) {
                    count += _asserts[method][block].Count - 1;
                }
                else {
                    return block;
                }
            }
            return null;
        }

        private int CountAsserts(Method method)
        {
            int count = 0;
            foreach (var block in _asserts[method].Keys) {
                count += _asserts[method][block].Count;
            }
            return count;
        }

        public Dictionary<Method, List<List<AssertStmt>>> TestDifferentRemovals()
        {
            Dictionary<Method, List<List<AssertStmt>>> returnData = new Dictionary<Method, List<List<AssertStmt>>>();
            foreach (Method method in _asserts.Keys) {
                List<List<AssertStmt>> solutions = new List<List<AssertStmt>>();
                TestAssertRemovalOrdering(0, solutions, new List<AssertStmt>(), method);
                returnData.Add(method, solutions);
            }
            return returnData;
        }

        private void TestAssertRemovalOrdering(int index, List<List<AssertStmt>> solutions, List<AssertStmt> currentSolution, Method method)
        {
            if (index == CountAsserts(method)) {
                solutions.Add(new List<AssertStmt>(currentSolution));
                return;
            }

            var parent = GetParentByIndex(index, method);
            var assert = GetAssertByIndex(index, method);

            if (parent is BlockStmt) {
                var block = (BlockStmt) parent;
                int assertPos = block.Body.IndexOf(assert);
                block.Body.Remove(assert);
                if (IsProgramValid()) {
                    var newCurrentSolution = new List<AssertStmt>(currentSolution) {assert}; //create a copy of the currentSolution and add in the assert
                    TestAssertRemovalOrdering(index + 1, solutions, newCurrentSolution, method);
                    block.Body.Insert(assertPos, assert);
                    TestAssertRemovalOrdering(index + 1, solutions, currentSolution, method);
                }
                else {
                    block.Body.Insert(assertPos, assert);
                    TestAssertRemovalOrdering(index + 1, solutions, currentSolution, method);
                }
            }
            else if (parent is MatchStmt) {
                var matchStmt = (MatchStmt) parent;
                bool found = false;
                foreach (var matchCase in matchStmt.Cases) {
                    if (matchCase.Body.Contains(assert)) {
                        found = true;
                        int assertPos = matchCase.Body.IndexOf(assert);
                        matchCase.Body.Remove(assert);
                        if (IsProgramValid()) {
                            var newCurrentSolution = new List<AssertStmt>(currentSolution) {assert}; //create a copy of the currentSolution and add in the assert
                            TestAssertRemovalOrdering(index + 1, solutions, newCurrentSolution, method);
                            matchCase.Body.Insert(assertPos, assert);
                            TestAssertRemovalOrdering(index + 1, solutions, currentSolution, method);
                        }
                        else {
                            matchCase.Body.Insert(assertPos, assert);
                            TestAssertRemovalOrdering(index + 1, solutions, currentSolution, method);
                        }
                    }
                }
                if (!found) {
                    throw new Exception("assert not found in match case");
                }
            }
        }

        /// <summary>
        /// Removes unnecessary parts of asserts (e.g. combined by && where one part is not needed)
        /// </summary>
        /// <returns></returns>
        public List<Tuple<AssertStmt, AssertStmt>> GetSimplifiedAsserts()
        {
            var simplifiedAsserts = new List<Tuple<AssertStmt, AssertStmt>>();

            foreach (var method in _asserts.Keys) {
                Console.WriteLine("Simplifying " + method.Name);
                foreach (Statement stmt in _asserts[method].Keys) {
                    if (!(stmt is BlockStmt)) continue; //TODO: Add for match statements
                    var bl = (BlockStmt) stmt;
                    foreach (AssertStmt assert in _asserts[method][stmt]) {
                        //Check and see if it is an AND operation - if not, continue
                        if (assert.Expr is BinaryExpr) {
                            var binExpr = (BinaryExpr) assert.Expr;
                            if (binExpr.Op != BinaryExpr.Opcode.And) {
                                continue;
                            }
                        }
                        int index = bl.Body.IndexOf(assert);
                        bl.Body.Remove(assert);
                        if (!IsProgramValid()) {
                            //Break down the asserts
                            var brokenAsserts = BreakDownExpr(assert);
                            //Add them back in
                            foreach (var brokenAssert in brokenAsserts) {
                                bl.Body.Insert(index, brokenAssert);
                            }
                            brokenAsserts.Reverse();
                            //Test to see which can be removed
                            for (int i = brokenAsserts.Count - 1; i >= 0; i--) {
                                int j = bl.Body.IndexOf(brokenAsserts[i]);
                                bl.Body.Remove(brokenAsserts[i]);
                                if (IsProgramValid()) {
                                    brokenAsserts.Remove(brokenAsserts[i]); //Item was removed successfully
                                }
                                else {
                                    bl.Body.Insert(j, brokenAsserts[i]); //Item could not be removed - reinsert
                                }
                            }
                            simplifiedAsserts.Add(new Tuple<AssertStmt, AssertStmt>(assert, CombineAsserts(brokenAsserts)));
                        }
                        else {
                            Console.WriteLine("Item can be completely removed separately");
                        }
                    }
                }
            }

            return simplifiedAsserts;
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
            //Need to do combine attributes somehow?
            Expression left = brokenAsserts[0].Expr;
            Expression right = CombineAsserts(brokenAsserts).Expr;
            BinaryExpr binExpr = new BinaryExpr(left.tok, BinaryExpr.Opcode.And, left, right);
            AssertStmt newAssert = new AssertStmt(assert.Tok, assert.EndTok, binExpr, assert.Attributes);
            return newAssert;
        }

        /// <summary>
        /// Breaks down an assert statement based off of && operators
        /// </summary>
        /// <param name="assert">The statement to break down</param>
        /// <returns>a list of new assert statements that can be separateley tested</returns>
        private List<AssertStmt> BreakDownExpr(AssertStmt assert)
        {
            var brokenAsserts = new List<AssertStmt>();
            if (assert.Expr is BinaryExpr) {
                BinaryExpr expr = (BinaryExpr) assert.Expr;
                if (expr.Op == BinaryExpr.Opcode.And) {
                    AssertStmt newAssert = new AssertStmt(expr.tok, assert.EndTok, expr.E0, assert.Attributes);
                    AssertStmt newAssert2 = new AssertStmt(expr.tok, assert.EndTok, expr.E1, assert.Attributes);

                    brokenAsserts.AddRange(BreakDownExpr(newAssert));
                    brokenAsserts.AddRange(BreakDownExpr(newAssert2));
                    return brokenAsserts;
                }
            }
            brokenAsserts.Add(assert);
            return brokenAsserts;
        }

        public List<AssertStmt> FindRemovableAsserts()
        {
            List<AssertStmt> removedAsserts = new List<AssertStmt>();
            if (!IsProgramValid()) {
                Console.WriteLine("Program " + Program.FullName + " cannot verify -> cannot remove asserts until it is fixed");
                return null;
            }
            foreach (var method in _asserts.Keys)
                removedAsserts.AddRange(FindRemovableAssertsInMethod(method));
            return removedAsserts;
        }

        private List<AssertStmt> FindRemovableAssertsInMethod(Method method)
        {
            List<AssertStmt> removedAsserts = new List<AssertStmt>();
            foreach (Statement stmt in _asserts[method].Keys) {
                if (stmt is BlockStmt)
                    removedAsserts.AddRange(FindRemovableAssertInBlockStmt((BlockStmt) stmt, method));
                else if (stmt is MatchStmt)
                    removedAsserts.AddRange(FindRemovableAssertsInMatchStmt((MatchStmt) stmt, method));
            }
            return removedAsserts;
        }

        private List<AssertStmt> FindRemovableAssertsInMatchStmt(MatchStmt stmt, Method method)
        {
            List<AssertStmt> removedAsserts = new List<AssertStmt>();
            foreach (AssertStmt assert in _asserts[method][stmt]) {
                foreach (MatchCaseStmt mcs in stmt.Cases) {
                    if (!mcs.Body.Contains(assert)) continue;
                    removedAsserts.AddRange(TryRemoveAssert(mcs.Body, mcs.Body.IndexOf(assert)));
                    break;
                }
            }
            return removedAsserts;
        }

        private List<AssertStmt> FindRemovableAssertInBlockStmt(BlockStmt stmt, Method method)
        {
            List<AssertStmt> removedAsserts = new List<AssertStmt>();
            foreach (AssertStmt assert in _asserts[method][stmt])
                removedAsserts.AddRange(TryRemoveAssert(stmt.Body, stmt.Body.IndexOf(assert)));
            return removedAsserts;
        }

        private List<AssertStmt> TryRemoveAssert(List<Statement> parent, int position)
        {
            List<AssertStmt> removedAsserts = new List<AssertStmt>();
            var assert = (AssertStmt)parent[position];
            parent.Remove(assert);
            if (!IsProgramValid())
                parent.Insert(position, assert);
            else if (!removedAsserts.Contains(assert)) 
                removedAsserts.Add(assert);
            return removedAsserts;
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
}
