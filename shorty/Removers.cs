using System;
using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using Microsoft.Dafny;

namespace shorty
{
    internal class SimpleVerifier
    {
        public void BoogieErrorInformation(Microsoft.Boogie.ErrorInformation errorInfo) {}

        private Program CloneProgram(Program program)
        {
            var cloner = new Cloner();
            var moduleDecl = new LiteralModuleDecl(cloner.CloneModuleDefinition(program.DefaultModuleDef, program.Name), null);
            return new Program(program.FullName, moduleDecl, program.BuiltIns, new InvisibleErrorReproter());
        }

        public bool IsProgramValid(Program program)
        {
            return IsProgramValid(program, null);
        }

        public bool IsProgramValid(Program program, Microsoft.Boogie.ErrorReporterDelegate errorDelegate)
        {
            
            try{
                var programId = "main_program_id";
                var stats = new Microsoft.Boogie.PipelineStatistics();
                var translator = new Translator(new InvisibleErrorReproter());
                var programCopy = CloneProgram(program);
                var resolver = new Resolver(programCopy);
                resolver.ResolveProgram(programCopy);
                var boogieProgram = translator.Translate(programCopy);
                var bplFileName = "bplFile";
                Microsoft.Boogie.LinearTypeChecker ltc;
                Microsoft.Boogie.CivlTypeChecker ctc;

                var oc = Microsoft.Boogie.ExecutionEngine.ResolveAndTypecheck(boogieProgram, bplFileName, out ltc, out ctc);
                if (oc != Microsoft.Boogie.PipelineOutcome.ResolvedAndTypeChecked) return false;

                Microsoft.Boogie.ExecutionEngine.EliminateDeadVariables(boogieProgram);
                Microsoft.Boogie.ExecutionEngine.CollectModSets(boogieProgram);
                Microsoft.Boogie.ExecutionEngine.CoalesceBlocks(boogieProgram);
                Microsoft.Boogie.ExecutionEngine.Inline(boogieProgram);

                oc = Microsoft.Boogie.ExecutionEngine.InferAndVerify(boogieProgram, stats, programId, errorDelegate);
                var allOk = stats.ErrorCount == 0 && stats.InconclusiveCount == 0 && stats.TimeoutCount == 0 && stats.OutOfMemoryCount == 0;
                //Console.WriteLine(allOk ? "Verification Successful" : "Verification failed");
                return oc == Microsoft.Boogie.PipelineOutcome.VerificationCompleted && allOk;
            }
            catch (Exception e) {
                //Console.WriteLine("Verification failed: " + e.Message);
                return false;
            }
        }
    }

    class RemovableTypesInMember
    {
        public MemberDecl Member { get; private set; }
        public readonly List<Wrap<Statement>> Asserts = new List<Wrap<Statement>>();
        public readonly List<Wrap<MaybeFreeExpression>> Invariants = new List<Wrap<MaybeFreeExpression>>();
        public readonly List<Wrap<Expression>> Decreases = new List<Wrap<Expression>>();
        public readonly List<WildCardDecreases> WildCardDecreaseses = new List<WildCardDecreases>();
        public readonly List<Wrap<Statement>> LemmaCalls = new List<Wrap<Statement>>();
        public readonly List<Wrap<Statement>> Calcs = new List<Wrap<Statement>>();

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

    class CalcRemover
    {
        SimpleVerifier verifier = new SimpleVerifier();

        private Program _program;

        public CalcRemover(Program program)
        {
            _program = program;
        }

        public Tuple<List<Expression>, List<BlockStmt>, List<CalcStmt.CalcOp>, List<CalcStmt>> Remove(Dictionary<MemberDecl, List<Wrap<Statement>>> memberWrapDictionary)
        {
            var removableLines = new List<Expression>();
            var removableHints = new List<BlockStmt>();
            var removableOps = new List<CalcStmt.CalcOp>();
            var removableCalcStmts = new List<CalcStmt>();
            foreach (var calcList in memberWrapDictionary.Values) {
                foreach (var calcWrap in calcList) {
                    var remover = new OneAtATimeRemover(_program);
                    if (remover.TryRemove(calcWrap)) {
                        removableCalcStmts.Add((CalcStmt) calcWrap.Removable);
                        continue;
                    }
                    var calcResults = RemoveFromCalc((CalcStmt) calcWrap.Removable);
                    removableLines.AddRange(calcResults.Item1);
                    removableHints.AddRange(calcResults.Item2);
                    removableOps.AddRange(calcResults.Item3);
                }
            }
            return new Tuple<List<Expression>, List<BlockStmt>, List<CalcStmt.CalcOp>, List<CalcStmt>>(removableLines, removableHints, removableOps, removableCalcStmts);
        }

        public Tuple<List<Expression>, List<BlockStmt>, List<CalcStmt.CalcOp>> RemoveFromCalc(CalcStmt calc)
        {
            var removableLines = new List<Expression>();
            var removableHints = new List<BlockStmt>();
            var removableOps = new List<CalcStmt.CalcOp>();
            var stepOps = calc.StepOps;
            var lines = calc.Lines;
            var hints = calc.Hints;

            //find lines and associated hints that can be removed
            // We don't want to touch the last two (dummy and last item)
            for (var i = 1; i < lines.Count - 2; i++) {
                var line = lines[i];
                for (int j = 0; j < hints.Count; j++) {
                    var hint = hints[j];
                    var stepOp = stepOps[j];
                    if (!TryRemove(new Wrap<Expression>(line, lines), new Wrap<BlockStmt>(hint, hints), new Wrap<CalcStmt.CalcOp>(stepOp, stepOps))) continue;
                    i--; //We have to go back one as a line has been removed all following ones will be moved back aswell
                    removableLines.Add(line);
                    removableOps.Add(stepOp);
                    if (hint.Body.Count > 0) //Don't need to return hints that are already "invisible"
                        removableHints.Add(hint);
                    break;
                }
            }

            //find other hints that can be removed
            foreach (var hint in hints) {
                if (hint.Body.Count == 0) continue;
                List<Statement> body = new List<Statement>();
                CloneTo(hint.Body, body);
                //emptyTheBody - have to do it this way as it is readonly
                for (int i = 0; i < hint.Body.Count; i++) {
                    var item = hint.Body[i];
                    hint.Body.Remove(item);
                }
                if (verifier.IsProgramValid(_program)) {
                    removableHints.Add(hint);
                }
                else {
                    CloneTo(body, hint.Body);
                }
            }

            return new Tuple<List<Expression>, List<BlockStmt>, List<CalcStmt.CalcOp>>(removableLines, removableHints, removableOps);
        }

        public static void CloneTo(List<Statement> listToClone, List<Statement> listToCloneInto)
        {
            Contract.Requires(listToClone != null);
            //Clear out list
            foreach (var item in listToCloneInto) {
                listToCloneInto.Remove(item);
            }
            foreach (var item in listToClone) {
                listToCloneInto.Add(item);
            }
        }

        public bool TryRemove(Wrap<Expression> line, Wrap<BlockStmt> hint, Wrap<CalcStmt.CalcOp> op)
        {
            var lineIndex = line.ParentList.IndexOf(line.Removable);
            var hintIndex = hint.ParentList.IndexOf(hint.Removable);
            var opIndex = op.ParentList.IndexOf(op.Removable);
            // We should also never be trying to remove the first or last line
            Contract.Assert(lineIndex != 0);
            Contract.Assert(lineIndex != line.ParentList.Count - 1);
            line.ParentList.Remove(line.Removable);
            hint.ParentList.Remove(hint.Removable);
            op.ParentList.Remove(op.Removable);
            if (verifier.IsProgramValid(_program))
                return true;
            line.ParentList.Insert(lineIndex, line.Removable);
            hint.ParentList.Insert(hintIndex, hint.Removable);
            op.ParentList.Insert(opIndex, op.Removable);
            //TODO: try and remove everything inside the hint
            return false;
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

    internal class SimultaneousMethodRemover : IRemover
    {
        // Goes though each method, removes one thing then verifies and reinserts from the error messages
        private readonly Program _program;
        private readonly SimpleVerifier _simpleVerifier = new SimpleVerifier();

        internal class SimilRemoverStorage<T>
        {
            public Dictionary<MemberDecl, Tuple<Wrap<T>, int>> LastRemovedItem = new Dictionary<MemberDecl, Tuple<Wrap<T>, int>>();

            public void ErrorInformation(Microsoft.Boogie.ErrorInformation errorInfo)
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

        public SimultaneousMethodRemover(Program program)
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
                    if (memberWrapDictionary[method].Count <= index) continue;
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

        private Tuple<Wrap<T>, int> RemoveOne<T>(Wrap<T> wrap)
        {
            int position = wrap.ParentList.IndexOf(wrap.Removable);
            wrap.ParentList.Remove(wrap.Removable);
            return new Tuple<Wrap<T>, int>(wrap, position);
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
            foreach (var wrap in itemWraps) {
                var simplifiedItem = TrySimplifyItem(wrap);
                if(simplifiedItem==null) continue;
                simplifiedItems.Add(simplifiedItem);
            }
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
            if (!_verifier.IsProgramValid(_program)) {
                return SimplifyItem(wrap, index);
            }
            Console.WriteLine("Whole assert can be completely removed separately"); //TODO figure out what to do here (remove from _removableItems?)
            return null;
        }

        private Tuple<T, T> SimplifyItem<T>(Wrap<T> wrap, int index)
        {
            var brokenItems = BreakAndReinsertItem(wrap, index);
            //brokenItems.Reverse();
            var itemRemoved = false;
            //Test to see which can be removed
            //TODO: remove the removable from the wrap? theres some kind of bug going on in here - what returns is ok but the original is not changed somehow
            for (var assertNum = brokenItems.Count - 1; assertNum >= 0; assertNum--) {
                var brokenItem = brokenItems[assertNum];
                Wrap<T> brokenWrap = new Wrap<T>(brokenItem, wrap.ParentList);
                if (!_remover.TryRemove(brokenWrap)) continue;
                brokenItems.Remove(brokenItem);
                itemRemoved = true;
            }
            return itemRemoved ? new Tuple<T, T>(wrap.Removable, CombineItems(brokenItems)) : null;
        }

        private List<T> BreakAndReinsertItem<T>(Wrap<T> wrap, int index)
        {
            var brokenAsserts = BreakDownExpr(wrap.Removable);
            foreach (var brokenAssert in brokenAsserts) {
                wrap.ParentList.Insert(index, brokenAssert);
            }
            return brokenAsserts;
        }

        private List<T> BreakDownExpr<T>(T item)
        {
            var brokenItems = new List<T>();
            var binaryExpr = GetExpr(item) as BinaryExpr;
            if (binaryExpr == null || binaryExpr.Op != BinaryExpr.Opcode.And) {
                brokenItems.Add(item);
                return brokenItems;
            }
            var newItem1 = GetNewNodeFromExpr(item, binaryExpr, binaryExpr.E0);
            var newItem2 = GetNewNodeFromExpr(item, binaryExpr, binaryExpr.E1);
            brokenItems.AddRange(BreakDownExpr(newItem1));
            brokenItems.AddRange(BreakDownExpr(newItem2));
            return brokenItems;
        }

        private Expression GetExpr<T>(T removable)
        {
            var assert = removable as AssertStmt;
            if (assert != null) {
                return assert.Expr;
            }
            var invariant = removable as MaybeFreeExpression;
            if (invariant != null) {
                return invariant.E;
            }
            return null;
        }

        private T GetNewNodeFromExpr<T>(T brokenItem, BinaryExpr binExpr, Expression subExpr)
        {
            var assert = brokenItem as AssertStmt;
            if (assert != null) {
                return (T) (object) new AssertStmt(binExpr.tok, assert.EndTok, subExpr, assert.Attributes);
            }
            var invariant = brokenItem as MaybeFreeExpression;
            if (invariant != null) {
                return (T) (object) new MaybeFreeExpression(subExpr);
            }
            return default(T);
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

        private T GetNewNodeFromItem<T>(T brokenItem, BinaryExpr binExpr)
        {
            var assert = brokenItem as AssertStmt;
            if (assert != null) {
                return (T) (object) new AssertStmt(assert.Tok, assert.EndTok, binExpr, assert.Attributes);
            }
            var invariant = brokenItem as MaybeFreeExpression;
            if (invariant != null) {
                return (T) (object) new MaybeFreeExpression(binExpr);
            }
            return default(T);
        }
    }
}
