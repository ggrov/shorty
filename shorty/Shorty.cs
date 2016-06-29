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
        //private readonly Dictionary<Statement, List<AssertStmt>> _andAsserts = new Dictionary<Statement, List<AssertStmt>>();
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
            if (_allMethods.ContainsKey(module))
                return;
            _allMethods.Add(module, new Dictionary<ClassDecl, List<Method>>());
            foreach (var decl in module.TopLevelDecls)
               IdentifyTopLevelDecl(decl, module);
        }

        private void IdentifyTopLevelDecl(Declaration decl, ModuleDefinition module)
        {
            if (decl is ClassDecl)
                IdentifyClass((ClassDecl)decl, module);
            else if (decl is LiteralModuleDecl){
                LiteralModuleDecl literalModule = (LiteralModuleDecl)decl;
                IdentifyModule(literalModule.ModuleDef);
            }
        }

        private void IdentifyClass(ClassDecl classDecl, ModuleDefinition module)
        {
            _allMethods[module].Add(classDecl, new List<Method>());
            foreach (var member in classDecl.Members)
                if (member is Method)
                    _allMethods[module][classDecl].Add((Method) member);
        }

        private void FindRemovableTypesInModule(ModuleDefinition module)
        {
            foreach (var decl in module.TopLevelDecls) {
                if (decl is ClassDecl)
                    FindRemovableTypesInClass((ClassDecl) decl, module);
                else if (decl is LiteralModuleDecl) {
                    LiteralModuleDecl literalModule = (LiteralModuleDecl) decl;
                    FindRemovableTypesInModule(literalModule.ModuleDef);
                }
            }
        }

        private void FindRemovableTypesInClass(ClassDecl classDecl, ModuleDefinition module)
        {
            foreach (var member in classDecl.Members) {
                FindRemovableTypesInMember(member, classDecl, module);
            }
        }

        private void FindRemovableTypesInMember(MemberDecl member, ClassDecl classDecl, ModuleDefinition module)
        {
            WildCardDecreases wildCardParent = null; // The parent of the current wildCard we are tracking
            FindDecreasesTypesInMember(member, ref wildCardParent);
            var method = member as Method;
            if (method != null) 
                FindRemovableTypesInMethod(method, wildCardParent, classDecl, module);
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

        private void FindRemovableTypesInMethod(Method method, WildCardDecreases wildCardParent, ClassDecl classDecl, ModuleDefinition module)
        {
            var block = method.Body;
            foreach (var statement in block.Body)
                FindRemovableTypesInStatement(statement, block, method, wildCardParent, classDecl, module);
        }

        private void FindRemovableTypesInStatement(Statement statement, Statement parent, Method method, WildCardDecreases wildCardParent, ClassDecl classDecl, ModuleDefinition module)
        {
            if (statement is AssertStmt)
                FindRemovableTypesInAssertStmt((AssertStmt)statement, parent, method);
            else if (statement is BlockStmt) {
                BlockStmt blockStmt = (BlockStmt) statement;
                foreach (var stmt in blockStmt.Body) {
                    FindRemovableTypesInStatement(stmt, statement, method, wildCardParent, classDecl, module);
                }
            }
            else if (statement is IfStmt) {
                IfStmt ifstmt = (IfStmt) statement;
                FindRemovableTypesInStatement(ifstmt.Thn, statement, method, wildCardParent, classDecl, module);
                FindRemovableTypesInStatement(ifstmt.Els, statement, method, wildCardParent, classDecl, module);
            }
            else if (statement is LoopStmt) {
                LoopStmt loopStmt = (LoopStmt) statement;
                GetLoopInvariants(loopStmt);
                wildCardParent = GetDecreasesLoop(loopStmt, method, wildCardParent);
                if (loopStmt is WhileStmt) {
                    WhileStmt whileStmt = (WhileStmt) loopStmt;
                    FindRemovableTypesInStatement(whileStmt.Body, statement, method, wildCardParent, classDecl, module);
                }
            }
            else if (statement is MatchStmt) {
                MatchStmt match = (MatchStmt) statement;
                foreach (MatchCaseStmt matchCase in match.Cases) {
                    foreach (Statement stmt in matchCase.Body) {
                        FindRemovableTypesInStatement(stmt, statement, method, wildCardParent, classDecl, module);
                    }
                }
            }
            else if (statement is ForallStmt) {
                ForallStmt forall = (ForallStmt) statement;
                FindRemovableTypesInStatement(forall.Body, statement, method, wildCardParent, classDecl, module);
            }
            else if (statement is CalcStmt) {
                CalcStmt calc = (CalcStmt) statement;
                foreach (var hint in calc.Hints) {
                    FindRemovableTypesInStatement(hint, statement, method, wildCardParent, classDecl, module);
                }
            }
            else if (statement is UpdateStmt)
                FindRemovableTypesInUpdateStmt((UpdateStmt) statement, parent, classDecl, module);
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

        private void FindRemovableTypesInUpdateStmt(UpdateStmt updateStmt, Statement parent, ClassDecl classDecl, ModuleDefinition module)
        {
            foreach (var expr in updateStmt.Rhss) {
                if(!IsAssignmentLemmaCall(expr, classDecl, module)) continue;
                if (!_lemmaCalls.ContainsKey(parent)) 
                    _lemmaCalls.Add(parent, new List<UpdateStmt>());
                _lemmaCalls[parent].Add(updateStmt);
            }
        }

        private bool IsAssignmentLemmaCall(AssignmentRhs expr, ClassDecl classDecl, ModuleDefinition module)
        {
            var exprRhs = expr as ExprRhs;
            if (exprRhs == null) return false;
            if (!(exprRhs.Expr is ApplySuffix)) return false;
            return IsCallToGhost((ApplySuffix)exprRhs.Expr, classDecl, module);
        }

        #endregion

        #region Lemma Calls

        private bool IsCallToGhost(SuffixExpr expr, ClassDecl classDecl, ModuleDefinition module)
        {
            var name = "";
            var nameSeg = expr.Lhs as NameSegment;
            if (nameSeg != null)
                name = nameSeg.Name;

            // Look through all the methods within the current scope and return whether it is ghost or not
            return (from method in _allMethods[module][classDecl] where method.Name == name select method.IsGhost).FirstOrDefault();
        }


        public List<UpdateStmt> FindRemovableLemmaCalls()
        {
            List<UpdateStmt> removableLemmaCalls = new List<UpdateStmt>();
            Statement parentStatement;
            foreach (Statement stmt in _lemmaCalls.Keys) {
                var blockStmt = stmt as BlockStmt;
                if (blockStmt != null)
                    foreach (var lemmaCall in LemmaCalls[blockStmt])
                        TryRemoveLemmaCall(blockStmt.Body, lemmaCall, removableLemmaCalls);
                else if (stmt is MatchStmt) {}
                //TODO: Somethign about match cases for lemma calls
            }
            return removableLemmaCalls;
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

        private WildCardDecreases GetDecreasesLoop(LoopStmt loop, Method method, WildCardDecreases wildCardParent)
        {
            //Deal with wildcard decreases
            WildCardDecreases wcd = wildCardParent;
            int wildCardCount = 0;
            foreach (Expression expr in loop.Decreases.Expressions) {
                if (expr is WildcardExpr) {
                    wildCardCount++;
                    wcd = new WildCardDecreases(expr, loop.Decreases, wildCardParent);
                    if (wildCardParent != null) {
                        wildCardParent.SubDecreases.Add(wcd);
                    }
                    else {
                        //start a new tree as there is no current parent
                        wildCardDecreases.Add(wcd);
                    }
                }
            }

            // Deal with any normal decreases
            if (loop.Decreases.Expressions.Count > wildCardCount) {
                if (!_decreases.ContainsKey(method)) {
                    _decreases.Add(method, new Tuple<List<Expression>, Dictionary<LoopStmt, List<Expression>>>(new List<Expression>(), new Dictionary<LoopStmt, List<Expression>>()));
                }
                if (!_decreases[method].Item2.ContainsKey(loop)) {
                    _decreases[method].Item2.Add(loop, new List<Expression>());
                }
                foreach (var expression in loop.Decreases.Expressions) {
                    if (!(expression is WildcardExpr)) {
                        _decreases[method].Item2[loop].AddRange(loop.Decreases.Expressions);
                    }
                }
            }
            return wcd;
        }

        public List<Expression> RemoveDecreasesFromParent(List<Expression> decreases)
        {
            List<Expression> removeableDecreases = new List<Expression>();

            for (int i = decreases.Count - 1; i >= 0; i--) {
                Expression expr = decreases[i];
                if (expr == null || expr is WildcardExpr) continue; //wildcards found afterwards
                decreases.Remove(expr);
                if (!IsProgramValid()) {
                    Console.WriteLine("\nCannot remove decreases at " + expr.tok.line + "\n");
                    decreases.Insert(i, expr);
                }
                else {
                    removeableDecreases.Add(expr);
                }
            }

            return removeableDecreases;
        }

        public List<Expression> FindRemoveableDecreases()
        {
            List<Expression> removeableDecreases = new List<Expression>();

            foreach (MemberDecl member in _decreases.Keys) {
                //Remove from member
                if (member is Method) {
                    var method = (Method) member;
                    removeableDecreases.AddRange(RemoveDecreasesFromParent(method.Decreases.Expressions));
                }
                else if (member is Function) {
                    var function = (Function) member;
                    removeableDecreases.AddRange(RemoveDecreasesFromParent(function.Decreases.Expressions));
                }
                foreach (var loop in _decreases[member].Item2.Keys) {
                    //remove from loops
                    removeableDecreases.AddRange(RemoveDecreasesFromParent(loop.Decreases.Expressions));
                }
            }

            removeableDecreases.AddRange(FindRemovableWildCards()); //remove wildcards

            return removeableDecreases;
        }

        private List<Expression> FindRemovableWildCards()
        {
            List<Expression> removableWildCards = new List<Expression>();
            foreach (var wcDecreases in wildCardDecreases) {
                removableWildCards.AddRange(FindRemovableWildCards(wcDecreases).Item1);
            }
            return removableWildCards;
        }

        public Tuple<List<Expression>, bool> FindRemovableWildCards(WildCardDecreases wcd)
        {
            var removableWildCards = new List<Expression>();
            bool valid = true; //makes sure it is valid to 
            //First off try and remove all lower wildcards
            foreach (var subDec in wcd.SubDecreases) {
                var removableWCs = FindRemovableWildCards(subDec);
                removableWildCards.AddRange(removableWCs.Item1);
                if (valid) {
                    valid = removableWCs.Item2;
                }
            }

            //at bottom level or all lower have been removed - safe to try and remove
            if (valid) {
                int index = wcd.ParentSpecification.Expressions.IndexOf(wcd.Expression);
                wcd.ParentSpecification.Expressions.Remove(wcd.Expression);
                if (IsProgramValid()) {
                    //successfully removed
                    removableWildCards.Add(wcd.Expression);
                }
                else {
                    valid = false;
                    wcd.ParentSpecification.Expressions.Insert(index, wcd.Expression);
                }
            }

            return new Tuple<List<Expression>, bool>(removableWildCards, valid);
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

            foreach (var loopStmt in _invariants.Keys) {
                List<MaybeFreeExpression> invariantList = _invariants[loopStmt];

                for (int i = invariantList.Count - 1; i >= 0; i--) {
                    if (invariantList[i] == null)
                        continue;
                    MaybeFreeExpression invariant = invariantList[i];
                    invariantList.Remove(invariant);
                    Console.WriteLine("Removing at line {0}", invariant.E.tok.line);
                    if (!IsProgramValid()) {
                        Console.WriteLine("Failed at line {0}", invariant.E.tok.line);
                        invariantList.Insert(i, invariant);
                    }
                    else {
                        removeableInvariants.Add(invariant);
                        Console.WriteLine("Succeeded at line {0}", invariant.E.tok.line);
                    }
                }
            }
            return removeableInvariants;
        }

        #endregion

        #region Asserts

        private AssertStmt GetAssertByIndex(int index, Method method)
        {
            int count = 0;
            foreach (var block in _asserts[method].Keys) {
                if (count + _asserts[method][block].Count - 1 < index) {
                    count += _asserts[method][block].Count - 1;
                }
                else {
                    return _asserts[method][block][index - count];
                }
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
                TestRemovals(0, solutions, new List<AssertStmt>(), method);
                returnData.Add(method, solutions);
            }
            return returnData;
        }

        private void TestRemovals(int index, List<List<AssertStmt>> solutions, List<AssertStmt> currentSolution, Method method)
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
                    TestRemovals(index + 1, solutions, newCurrentSolution, method);
                    block.Body.Insert(assertPos, assert);
                    TestRemovals(index + 1, solutions, currentSolution, method);
                }
                else {
                    block.Body.Insert(assertPos, assert);
                    TestRemovals(index + 1, solutions, currentSolution, method);
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
                            TestRemovals(index + 1, solutions, newCurrentSolution, method);
                            matchCase.Body.Insert(assertPos, assert);
                            TestRemovals(index + 1, solutions, currentSolution, method);
                        }
                        else {
                            matchCase.Body.Insert(assertPos, assert);
                            TestRemovals(index + 1, solutions, currentSolution, method);
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
//or or statements or anything else???
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

        public List<AssertStmt> FindUnnecessaryAsserts()
        {
            List<AssertStmt> removedAsserts = new List<AssertStmt>();

            if (!IsProgramValid()) {
                Console.WriteLine("Program " + Program.FullName + " cannot verify -> cannot remove asserts until it is fixed");
                return null;
            }

            //go through each block

            foreach (var method in _asserts.Keys) {
                foreach (Statement stmnt in _asserts[method].Keys) {
                    if (stmnt is BlockStmt) {
                        BlockStmt bl = (BlockStmt) stmnt;
                        foreach (AssertStmt assert in _asserts[method][stmnt]) {
                            int index = bl.Body.IndexOf(assert);
                            bl.Body.Remove(assert);
                            if (!IsProgramValid()) {
                                bl.Body.Insert(index, assert);
                            }
                            else if (!removedAsserts.Contains(assert)) {
                                removedAsserts.Add(assert);
                            }
                        }
                    }
                    // Match statements are not stored in a block or inherited from notmal statements so we need a special case from them
                    else if (stmnt is MatchStmt) {
                        MatchStmt ms = (MatchStmt) stmnt;
                        foreach (AssertStmt assert in _asserts[method][stmnt]) {
                            foreach (MatchCaseStmt mcs in ms.Cases) {
                                mcs.Body.Remove(assert);
                                if (!removedAsserts.Contains(assert)) {
                                    removedAsserts.Add(assert);
                                }
                                if (!IsProgramValid()) {
                                    mcs.Body.Add(assert);
                                }
                                else {
                                    if (!removedAsserts.Contains(assert)) {
                                        removedAsserts.Add(assert);
                                    }
                                }
                            }
                        }
                    }
                }
            }
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
            Contract.Requires(Program != null);
            string programId = "main_program_id";
            Bpl.PipelineStatistics stats = new Bpl.PipelineStatistics();

            var translator = new Translator(new ConsoleErrorReporter());
            Program programCopy = CloneProgram(Program);

            var resolver = new Resolver(programCopy);
            try {
                resolver.ResolveProgram(programCopy);
            }
            catch {
                Console.WriteLine("Failed to resolve program");
                return false;
            }

            Bpl.Program boogieProgram;
            try {
                boogieProgram = translator.Translate(programCopy);
            }
            catch {
                Console.WriteLine("Program " + programCopy.FullName + "failed to translate.");
                return false;
            }

            var bplFileName = "bplFile";
            Bpl.LinearTypeChecker ltc;
            Bpl.CivlTypeChecker ctc;

            var oc = Bpl.ExecutionEngine.ResolveAndTypecheck(boogieProgram, bplFileName, out ltc, out ctc);
            switch (oc) {
                case Bpl.PipelineOutcome.ResolutionError:
                    return false;
                case Bpl.PipelineOutcome.TypeCheckingError:
                    return false;
                case Bpl.PipelineOutcome.ResolvedAndTypeChecked:
                    Bpl.ExecutionEngine.EliminateDeadVariables(boogieProgram);
                    Bpl.ExecutionEngine.CollectModSets(boogieProgram);
                    Bpl.ExecutionEngine.CoalesceBlocks(boogieProgram);
                    Bpl.ExecutionEngine.Inline(boogieProgram);

                    Bpl.ErrorReporterDelegate er = BoogieErrorInformation;
                    try {
                        oc = Bpl.ExecutionEngine.InferAndVerify(boogieProgram, stats, programId, er);
                    }
                    catch {
                        Console.WriteLine("Verification caused exception");
                        return false;
                    }
                    var allOk = stats.ErrorCount == 0 && stats.InconclusiveCount == 0 && stats.TimeoutCount == 0 && stats.OutOfMemoryCount == 0;
                    if (!allOk) {
                        //The program failed to verify - we must now find the allAsserts from the list of tokens we got.
                        Console.WriteLine("Verification failed");
                    }
                    switch (oc) {
                        case Bpl.PipelineOutcome.VerificationCompleted:
                            if (allOk) Console.WriteLine("Verification successful");
                            return allOk;

                        case Bpl.PipelineOutcome.Done:
                            if (allOk) Console.WriteLine("Verification successful");
                            return allOk;
                        default:
                            return false;
                    }
                case Bpl.PipelineOutcome.FatalError:
                    return false;
                case Bpl.PipelineOutcome.VerificationCompleted:
                    return true;
                default:
                    return false;
            }
        }

        #endregion
    }
}
