using System;
using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Net;
using System.Resources;
using System.Text;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.Dafny;
using NUnit.Framework;
using NUnit.Framework.Internal.Execution;
using Function = Microsoft.Dafny.Function;
using Program = Microsoft.Dafny.Program;

namespace shorty
{
    internal class SimpleVerifier
    {
        public void BoogieErrorInformation(Microsoft.Boogie.ErrorInformation errorInfo) {}

        private Program CloneProgram(Program program)
        {
            var cloner = new Cloner();
            var moduleDecl = new LiteralModuleDecl(cloner.CloneModuleDefinition(program.DefaultModuleDef, program.Name), null);
            return new Program(program.FullName, moduleDecl, program.BuiltIns, new InvisibleErrorReporter());
        }

        public bool IsProgramValid(Program program)
        {
            return IsProgramValid(program, null);
        }

        public bool IsProgramValid(Program program, Microsoft.Boogie.ErrorReporterDelegate errorDelegate)
        {
            try {
                var programId = "main_program_id";
                var stats = new Microsoft.Boogie.PipelineStatistics();
                var translator = new Translator(new InvisibleErrorReporter());
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
            catch (Exception) {
                //Console.WriteLine("Verification failed: " + e.Message);
                return false;
            }
        }
    }

    public class RemovableTypesInMember
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
        public int Index { get; private set; }
        public bool Removed;

        public Wrap(T removable, List<T> parentList)
        {
            Contract.Requires(parentList.Contains(removable));
            Removable = removable;
            ParentList = parentList;
            Removed = false;
            Index = -1;
        }

        public void Remove()
        {
            if (Removed) return;
            Index = ParentList.IndexOf(Removable);
            if (Index < 0) throw new Exception("Removable item is not in its ParentList");
            ParentList.Remove(Removable);
            Removed = true;
        }

        public void Reinsert()
        {
            if (!Removed) return;
            ParentList.Insert(Index, Removable);
            Index = -1;
            Removed = false;
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

    public class WildCardDecreases
    {
        public readonly Expression Expression;
        public Wrap<Expression> ExpressionWrap;
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
            ExpressionWrap = new Wrap<Expression>(decreasesExpression, parentSpecification.Expressions);
        }
    }

    public class CalcRemover
    {
        private readonly SimpleVerifier _verifier = new SimpleVerifier();

        private readonly Program _program;

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
                for (var j = 0; j < hints.Count; j++) {
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
                var body = new List<Statement>();
                CloneTo(hint.Body, body);
                //emptyTheBody - have to do it this way as it is readonly
                for (var i = 0; i < hint.Body.Count; i++) {
                    var item = hint.Body[i];
                    hint.Body.Remove(item);
                }
                if (_verifier.IsProgramValid(_program)) {
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
            if (_verifier.IsProgramValid(_program))
                return true;
            line.ParentList.Insert(lineIndex, line.Removable);
            hint.ParentList.Insert(hintIndex, hint.Removable);
            op.ParentList.Insert(opIndex, op.Removable);
            //TODO: try and remove everything inside the hint
            return false;
        }
    }

    public interface IRemover
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
            if (!IsProgramValid(_program))
                throw new Exception("Program invalid after removal!");
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
            wrap.Remove();
            if (IsProgramValid(_program))
                return true;
            wrap.Reinsert();
            return false;
        }

        private static bool IsProgramValid(Program program)
        {
            var validator = new SimpleVerifier();
            return validator.IsProgramValid(program);
        }
    }

    /// <summary>
    /// Contains methods for dealing with the error information when 
    /// verification failed for reinserting the items on simultaneous 
    /// removal approaches
    /// </summary>
    abstract class VerificationErrorInformationRetriever
    {
        public abstract void ErrorInformation(ErrorInformation errorInfo);

        protected List<MemberDecl> AlreadyReAddedMembers = new List<MemberDecl>();

        protected MemberDecl FindMethod(int pos, IEnumerable<MemberDecl> members)
        {
            var memberDecls = members as IList<MemberDecl> ?? members.ToList();
            foreach (var member in memberDecls) {
                if (member.BodyStartTok.pos <= pos && member.BodyEndTok.pos >= pos)
                    return member;
                if (member.BodyStartTok.pos != 0 || member.BodyEndTok.pos != 0) continue; //Sometimes this bugs out... needs resolved first?
                var method = member as Method;
                if (method == null) continue;
                if (method.Body.Tok.pos <= pos && method.Body.EndTok.pos >= pos)
                    return member;
            }
            //The method could not be found - maybe the removal caused two errors so we already have fixed it? lets be sure
            foreach (var member in AlreadyReAddedMembers) {
                if (member.BodyStartTok.pos <= pos && member.BodyEndTok.pos >= pos)
                    throw new AlreadyRemovedException();
                if (member.BodyStartTok.pos != 0 || member.BodyEndTok.pos != 0) continue; //Sometimes this bugs out...
                var method = member as Method;
                if (method != null) {
                    if (method.Body.Tok.pos <= pos && method.Body.EndTok.pos >= pos)
                        throw new AlreadyRemovedException();
                    continue;
                }
            }
            //still hasn't been found.  Possible we're dealing with a function then
            //Functions have no end tokens - (assuming the BodyEndTok thing isn't working for whatever reason
            //we will look through all the functions and find the one with the highest pos that is less than the errors pos.
            Function currentFunction = null;
//            MemberDecl currentFunction = null;
            foreach (var memberDecl in memberDecls) {
                var function = memberDecl as Function;
                if (function == null) continue;
                if (function.tok.pos >= pos) continue; //function occurs after our token - no chance this is the one
                if (currentFunction == null)
                    currentFunction = function;
                else if (function.tok.pos > currentFunction.tok.pos)
                    currentFunction = function;
            }
            if (currentFunction != null) return currentFunction;
            //TODO is it possible something could have been removed in a field?
            throw new Exception("Could not find method"); //TODO:  this won't be caught as it is caught in boogie somewhere... will have to set a flag or something
        }
    }

    internal class SimultaneousMethodRemover : IRemover
    {
        // Goes though each method, removes one thing then verifies and reinserts from the error messages
        private readonly Program _program;
        private readonly SimpleVerifier _simpleVerifier = new SimpleVerifier();

        internal class SimilRemoverStorage<T> : VerificationErrorInformationRetriever
        {
            public Dictionary<MemberDecl, Wrap<T>> LastRemovedItem = new Dictionary<MemberDecl, Wrap<T>>();

            public override void ErrorInformation(Microsoft.Boogie.ErrorInformation errorInfo)
            {
                MemberDecl member = null;
                try {
                    member = FindMethod(errorInfo.Tok.pos, LastRemovedItem.Keys);
                }
                catch (AlreadyRemovedException) {
                    return;
                }
                catch (Exception) {
                    throw new Exception("Could not find member");
                }

                if (member == null) return;
                LastRemovedItem[member].Reinsert();
                AlreadyReAddedMembers.Add(member);
                LastRemovedItem.Remove(member);
            }
        }

        public SimultaneousMethodRemover(Program program)
        {
            _program = program;
        }

        public List<Wrap<T>> Remove<T>(Dictionary<MemberDecl, List<Wrap<T>>> memberWrapDictionary)
        {
            var removableWraps = new List<Wrap<T>>();
            var index = 0;
            var similRemover = new SimilRemoverStorage<T>();
            var finished = false;
            while (!finished) {
                finished = RemoveAndTrackItemsForThisRun(memberWrapDictionary, index++, similRemover);
                RunVerification(similRemover);
                ReinsertInvalidItems(similRemover, removableWraps);
                similRemover.LastRemovedItem = new Dictionary<MemberDecl, Wrap<T>>();
            }
            return removableWraps;
        }

        private static void ReinsertInvalidItems<T>(SimilRemoverStorage<T> similRemover, List<Wrap<T>> removableWraps)
        {
            foreach (var wrap in similRemover.LastRemovedItem.Values)
                removableWraps.Add(wrap);
        }

        private void RunVerification<T>(SimilRemoverStorage<T> similRemover)
        {
            _simpleVerifier.IsProgramValid(_program, similRemover.ErrorInformation);
        }

        private bool RemoveAndTrackItemsForThisRun<T>(Dictionary<MemberDecl, List<Wrap<T>>> memberWrapDictionary, int index, SimilRemoverStorage<T> similRemover)
        {
            var finished = true;
            foreach (var method in memberWrapDictionary.Keys) {
                if (memberWrapDictionary[method].Count <= index) continue; //All items in this method have been done
                var wrap = memberWrapDictionary[method][index];
                wrap.Remove();
                similRemover.LastRemovedItem.Add(method, wrap); //Track the item
                finished = false;
            }
            return finished;
        }
    }

    public class SimplificationWrapData
    {
        public List<Wrap<Statement>> RemovableAsserts = new List<Wrap<Statement>>();
        public List<Wrap<MaybeFreeExpression>> RemovableInvariants = new List<Wrap<MaybeFreeExpression>>() ;
        public List<Wrap<Expression>> RemovableDecreases = new List<Wrap<Expression>>();
        public List<Wrap<Statement>> RemovableLemmaCalls = new List<Wrap<Statement>>();
        public List<Wrap<Statement>> RemovableCalcs = new List<Wrap<Statement>>();
        public List<Tuple<Statement, Statement>> SimplifiedAsserts = new List<Tuple<Statement, Statement>>();
        public List<Tuple<MaybeFreeExpression, MaybeFreeExpression>> SimplifiedInvariants = new List<Tuple<MaybeFreeExpression, MaybeFreeExpression>>();
        public Tuple<List<Expression>, List<BlockStmt>, List<CalcStmt.CalcOp>> SimplifiedCalcs;

        public SimplificationData ToSimplificationData()
        {
            SimplificationData simpData = new SimplificationData();
            foreach (var assert in RemovableAsserts) {
                simpData.RemovableAsserts.Add((AssertStmt)assert.Removable);
            }
            foreach (var invariant in RemovableInvariants) {
                simpData.RemovableInvariants.Add(invariant.Removable);
            }
            foreach (var decreases in RemovableDecreases) {
                simpData.RemovableDecreases.Add(decreases.Removable);
            }
            foreach (var lemmaCall in RemovableLemmaCalls) {
                simpData.RemovableLemmaCalls.Add((UpdateStmt)lemmaCall.Removable);
            }
            foreach (var calc in RemovableCalcs) {
                simpData.RemovableCalcs.Add((CalcStmt)calc.Removable);
            }
            return simpData;
        }
    }
    public class SimplificationData
    {
        public List<AssertStmt> RemovableAsserts = new List<AssertStmt>();
        public List<MaybeFreeExpression> RemovableInvariants = new List<MaybeFreeExpression>();
        public List<Expression> RemovableDecreases = new List<Expression>();
        public List<UpdateStmt> RemovableLemmaCalls = new List<UpdateStmt>();
        public List<CalcStmt> RemovableCalcs = new List<CalcStmt>();
        public List<Tuple<Statement, Statement>> SimplifiedAsserts = new List<Tuple<Statement, Statement>>();
        public List<Tuple<MaybeFreeExpression, MaybeFreeExpression>> SimplifiedInvariants = new List<Tuple<MaybeFreeExpression, MaybeFreeExpression>>();
        public Tuple<List<Expression>, List<BlockStmt>, List<CalcStmt.CalcOp>> SimplifiedCalcs;
    }

    public class WildCardDecreasesRemover
    {
        private Program _program;

        public WildCardDecreasesRemover(Program program)
        {
            _program = program;
        }

        public List<WildCardDecreases> FindRemovableWildCards(List<WildCardDecreases> wildCardDecreaseses)
        {
            var removableWildCards = new List<WildCardDecreases>();
            foreach (var wcDecreases in wildCardDecreaseses)
                removableWildCards.AddRange(FindRemovableWildCards(wcDecreases).Item1);
            return removableWildCards;
        }

        private Tuple<List<WildCardDecreases>, bool> FindRemovableWildCards(WildCardDecreases currentWildCardDecreases)
        {
            var removableWildCards = new List<WildCardDecreases>();
            var safeToRemove = true;
            RemoveWildCardSubDecreases(currentWildCardDecreases, removableWildCards, ref safeToRemove);

            if (safeToRemove)
                RemoveWildCardDecreases(currentWildCardDecreases, removableWildCards, ref safeToRemove);

            return new Tuple<List<WildCardDecreases>, bool>(removableWildCards, safeToRemove);
        }

        private void RemoveWildCardDecreases(WildCardDecreases currentWildCardDecreases, List<WildCardDecreases> removableWildCards, ref bool safeToRemove)
        {
            var index = currentWildCardDecreases.ParentSpecification.Expressions.IndexOf(currentWildCardDecreases.Expression);
            currentWildCardDecreases.ParentSpecification.Expressions.Remove(currentWildCardDecreases.Expression);
            SimpleVerifier ver = new SimpleVerifier();
            if (ver.IsProgramValid(_program))
            {
                removableWildCards.Add(currentWildCardDecreases);
//                if (currentWildCardDecreases.ParentWildCardDecreases == null)
//                    _allRemovableTypes.RemoveWildCardDecreases(currentWildCardDecreases);
            }
            else
            {
                currentWildCardDecreases.ParentSpecification.Expressions.Insert(index, currentWildCardDecreases.Expression);
                safeToRemove = false;
            }
        }

        private void RemoveWildCardSubDecreases(WildCardDecreases wcd, List<WildCardDecreases> removableWildCards, ref bool safeToRemove)
        {
            foreach (var subDec in wcd.SubDecreases)
            {
                var removableWCs = FindRemovableWildCards(subDec);
                removableWildCards.AddRange(removableWCs.Item1);
                if (safeToRemove)
                    safeToRemove = removableWCs.Item2;
            }
        }
    }

    class MethodRemover
    {
        private readonly Program _program;

        public MethodRemover(Program program)
        {
            _program = program;
        }

        private bool IsProgramValid()
        {
            var verifier = new SimpleVerifier();
            return verifier.IsProgramValid(_program);
        }

        public SimplificationData FullSimplify(MemberDecl member)
        {
            var removableTypeFinder = new RemovableTypeFinder(_program);
            var removableTypesInMember = removableTypeFinder.FindRemovableTypesInMember(member);

            var simpData = new SimplificationData();
            foreach (var assert in RemoveItems(removableTypesInMember.Asserts)) 
                simpData.RemovableAsserts.Add((AssertStmt) assert);
            simpData.RemovableInvariants.AddRange(RemoveItems(removableTypesInMember.Invariants));
            simpData.RemovableDecreases.AddRange(RemoveItems(removableTypesInMember.Decreases));
            foreach (var lemmaCall in RemoveItems(removableTypesInMember.LemmaCalls)) 
                simpData.RemovableLemmaCalls.Add((UpdateStmt)lemmaCall);
            simpData.SimplifiedAsserts.AddRange(SimplifyItems(removableTypesInMember.Asserts));
            simpData.SimplifiedInvariants.AddRange(SimplifyItems(removableTypesInMember.Invariants));
            WildCardDecreasesRemover wcdRemover = new WildCardDecreasesRemover(_program);
            var wildCardDecreases = wcdRemover.FindRemovableWildCards(removableTypesInMember.WildCardDecreaseses);
            foreach (var wildCardDecrease in wildCardDecreases) {
                simpData.RemovableDecreases.Add(wildCardDecrease.Expression);
            }
            var calcLines = new List<Expression>();
            var calcBlocks = new List<BlockStmt>();
            var calcOps = new List<CalcStmt.CalcOp>();

            foreach (var wrap in removableTypesInMember.Calcs) {
                var simplifiedItem = SimplifyCalc((CalcStmt) wrap.Removable);
                if (simplifiedItem == null) continue;
                calcLines.AddRange(simplifiedItem.Item1);
                calcBlocks.AddRange(simplifiedItem.Item2);
                calcOps.AddRange(simplifiedItem.Item3);
            }
            simpData.SimplifiedCalcs = new Tuple<List<Expression>, List<BlockStmt>, List<CalcStmt.CalcOp>>(calcLines, calcBlocks, calcOps);
            return simpData;
            //TODO remove things from the allRemovableTypes?
        }

        private List<T> RemoveItems<T>(List<Wrap<T>> wraps)
        {
            var removables = new List<T>();
            for (var i = wraps.Count - 1; i >= 0; i--) {
                var wrap = wraps[i];
                if (!RemoveItem(wrap)) continue;
                removables.Add(wrap.Removable);
                wraps.Remove(wrap);
            }
            return removables;
        }

        private List<Tuple<T, T>> SimplifyItems<T>(List<Wrap<T>> wraps)
        {
            var simplifiedItems = new List<Tuple<T, T>>();
            for (var i = wraps.Count - 1; i >= 0; i--) {
                var wrap = wraps[i];
                var simplifiedItem = SimplifyItem(wrap);
                if (simplifiedItem == null) continue;
                simplifiedItems.Add(simplifiedItem);
                wraps.Remove(wrap);
                wraps.Add(new Wrap<T>(simplifiedItem.Item2, wrap.ParentList));
            }
            return simplifiedItems;
        }

        private bool RemoveItem<T>(Wrap<T> wrap)
        {
            var index = wrap.ParentList.IndexOf(wrap.Removable);
            wrap.ParentList.Remove(wrap.Removable);
            var worked = IsProgramValid();
            if (!worked) {
                wrap.ParentList.Insert(index, wrap.Removable);
            }
            return worked;
        }

        private Tuple<T, T> SimplifyItem<T>(Wrap<T> wrap)
        {
            var simplifier = new Simplifier(_program);
            var simplifiedWraps = simplifier.TrySimplifyItem(wrap);
            if (simplifiedWraps == null) return null;
            return new Tuple<T, T>(simplifiedWraps.Item1.Removable, simplifiedWraps.Item2.Removable);
        }

        private Tuple<List<Expression>, List<BlockStmt>, List<CalcStmt.CalcOp>> SimplifyCalc(CalcStmt calc)
        {
            var calcRemover = new CalcRemover(_program);
            return calcRemover.RemoveFromCalc(calc);
        }
    }

    class SimplificationItemInMethod
    {
        private enum Item
        {
            Assert,
            Invariant,
            Decreases,
            LemmaCall,
            Calc
        }

        private readonly Item _item;
        public MemberDecl Member;
        private Wrap<Statement> _assert;
        private Wrap<Statement> _lemmaCall;
        private Wrap<Statement> _calcs;
        private Wrap<MaybeFreeExpression> _invariant;
        private Wrap<Expression> _decreases;

        public SimplificationItemInMethod(MemberDecl member, Wrap<Statement> statement)
        {
            if (statement.Removable is AssertStmt) {
                _assert = statement;
                _item = Item.Assert;
            }
            else if (statement.Removable is UpdateStmt) {
                _lemmaCall = statement;
                _item = Item.LemmaCall;
            }
            else if (statement.Removable is CalcStmt) {
                _calcs = statement;
                _item = Item.Calc;
            }
            Member = member;
        }

        public SimplificationItemInMethod(MemberDecl member, Wrap<MaybeFreeExpression> invariant)
        {
            _invariant = invariant;
            _item = Item.Invariant;
            Member = member;
        }

        public SimplificationItemInMethod(MemberDecl member, Wrap<Expression> deceases)
        {
            _decreases = deceases;
            _item = Item.Decreases;
            Member = member;
        }

        public object GetItem()
        {
            switch (_item) {
                case Item.Assert:
                    return _assert;
                case Item.Invariant:
                    return _invariant;
                case Item.Decreases:
                    return _decreases;
                case Item.Calc:
                    return _calcs;
                case Item.LemmaCall:
                    return _lemmaCall;
                default:
                    throw new Exception("item enum not found!");
            }
        }
    }

    class SimultaneousAllTypeMethodRemover : VerificationErrorInformationRetriever
    {
        private readonly Program _program;
        private int _index = 0;
        private Dictionary<MemberDecl, SimplificationItemInMethod> _removedItemsOnRun = new Dictionary<MemberDecl, SimplificationItemInMethod>();

        public SimultaneousAllTypeMethodRemover(Program program)
        {
            _program = program;
        }

        public override void ErrorInformation(ErrorInformation errorInfo)
        {
            MemberDecl member = null;
            try {
                member = FindMethod(errorInfo.Tok.pos, _removedItemsOnRun.Keys);
            }
            catch (AlreadyRemovedException) {
                return;
            }
            catch (Exception) {
                throw new Exception("Could not find member");
            }

            if (member == null) return;
            var item = _removedItemsOnRun[member].GetItem();
            if (item is Wrap<Statement>) {
                ((Wrap<Statement>)item).Reinsert();
            }
            if (item is Wrap<MaybeFreeExpression>) {
                ((Wrap<MaybeFreeExpression>)item).Reinsert();
            }
            if (item is Wrap<Expression>) {
                ((Wrap<Expression>)item).Reinsert();
            }

            AlreadyReAddedMembers.Add(member);
            _removedItemsOnRun.Remove(member);
        }

        public SimplificationData Remove(Program program, AllRemovableTypes allRemovableTypes)
        {
            var objectWraps = new Dictionary<MemberDecl, List<SimplificationItemInMethod>>();
            foreach (var member in allRemovableTypes.RemovableTypesInMethods.Keys) {
                var removableTypeInMethod = allRemovableTypes.RemovableTypesInMethods[member];
                var itemsInMethod = removableTypeInMethod.Asserts.Select(item => new SimplificationItemInMethod(member, item)).ToList();
                itemsInMethod.AddRange(removableTypeInMethod.Invariants.Select(item => new SimplificationItemInMethod(member, item)));
                itemsInMethod.AddRange(removableTypeInMethod.Decreases.Select(item => new SimplificationItemInMethod(member, item)));
                itemsInMethod.AddRange(removableTypeInMethod.LemmaCalls.Select(item => new SimplificationItemInMethod(member, item)));
                itemsInMethod.AddRange(removableTypeInMethod.Calcs.Select(item => new SimplificationItemInMethod(member, item)));
                objectWraps.Add(member, itemsInMethod);
            }
            var simpWrapData = Remove(program, objectWraps);
            //TODO: remove the items in simpData from allRemoveableTypes
            foreach (var assert in simpWrapData.RemovableAsserts) {
                allRemovableTypes.RemoveAssert(assert);
            }
            foreach (var invariant in simpWrapData.RemovableInvariants) {
                allRemovableTypes.RemoveInvariant(invariant);
            }
            foreach (var decreases in simpWrapData.RemovableDecreases) {
                allRemovableTypes.RemoveDecreases(decreases);
            }
            foreach (var lemmaCall in simpWrapData.RemovableLemmaCalls) {
                allRemovableTypes.RemoveLemmaCall(lemmaCall);
            }
            foreach (var calc in simpWrapData.RemovableCalcs) {
                allRemovableTypes.RemoveCalc(calc);
            }
            WildCardDecreasesRemover wcdRemover = new WildCardDecreasesRemover(_program);
            
            var simplificationData = simpWrapData.ToSimplificationData();
            var removableWildCards = wcdRemover.FindRemovableWildCards(allRemovableTypes.WildCardDecreaseses.ToList());
            foreach (var wildCard in removableWildCards )
            {
                simplificationData.RemovableDecreases.Add(wildCard.Expression);
                allRemovableTypes.RemoveWildCardDecreases(wildCard);
            }
            return simplificationData;
        }

        private SimplificationWrapData Remove(Program program, Dictionary<MemberDecl, List<SimplificationItemInMethod>> simpItems)
        {
            var finished = false;
            var simpData = new SimplificationWrapData();
            while (!finished) {
                finished = RemoveAnItemFromEachMethod(simpItems);
                _index++;
                VerifyProgram();
                GatherSimpData(simpData);
                Reset();
            }
            //TODO: optimise by integrating wildcarddecreases with main task
            

            return simpData;
        }

        private void Reset()
        {
            AlreadyReAddedMembers = new List<MemberDecl>();
            _removedItemsOnRun = new Dictionary<MemberDecl, SimplificationItemInMethod>();

        }

        private void GatherSimpData(SimplificationWrapData simpData)
        {
            //everything still in itemsRemoved should be used for return
            foreach (var simplificationItemInMethod in _removedItemsOnRun.Values) {
                var item = simplificationItemInMethod.GetItem();
                if (item is Wrap<Statement>) {
                    var wrap = (Wrap<Statement>) item;
                    if (wrap.Removable is AssertStmt)
                        simpData.RemovableAsserts.Add(wrap);

                    else if (wrap.Removable is UpdateStmt)
                        simpData.RemovableLemmaCalls.Add(wrap);
                    else if (wrap.Removable is CalcStmt)
                        simpData.RemovableCalcs.Add(wrap);

                    else
                        throw new Exception("Cannot match removable statement to removable type");
                }
                else if (item is Wrap<MaybeFreeExpression>) {
                    var wrap = (Wrap<MaybeFreeExpression>) item;
                    simpData.RemovableInvariants.Add(wrap);
                }
                else if (item is Wrap<Expression>) {
                    var wrap = (Wrap<Expression>) item;
                    simpData.RemovableDecreases.Add(wrap);
                }
                else {
                    throw new Exception("Cannot match removed object to removable type");
                }
            }
        }

        private bool RemoveAnItemFromEachMethod(Dictionary<MemberDecl, List<SimplificationItemInMethod>> simpItems)
        {
            var finished = true;
            foreach (var member in simpItems.Keys) {
                var simpsInMethod = simpItems[member];
                if (!(_index < simpsInMethod.Count)) continue;
                var item = simpsInMethod[_index].GetItem();
                if (item is Wrap<Statement>)
                    ((Wrap<Statement>) item).Remove();
                else if (item is Wrap<MaybeFreeExpression>)
                    ((Wrap<MaybeFreeExpression>) item).Remove();
                else if (item is Wrap<Expression>)
                    ((Wrap<Expression>) item).Remove();
                else
                    throw new Exception("couldn't get wrap from member");
                _removedItemsOnRun.Add(member, simpsInMethod[_index]);
                finished = false;
                
            }
            return finished;
        }

        private void VerifyProgram()
        {
            var verifier = new SimpleVerifier();
            verifier.IsProgramValid(_program, ErrorInformation);
        }
    }

    class AlreadyRemovedException : Exception {}

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

        public List<Tuple<Wrap<T>, Wrap<T>>> GetSimplifiedItems<T>(IEnumerable<Wrap<T>> itemWraps)
        {
            var simplifiedItems = new List<Tuple<Wrap<T>, Wrap<T>>>();
            foreach (var wrap in itemWraps) {
                var simplifiedItem = TrySimplifyItem(wrap);
                if (simplifiedItem == null) continue;
                simplifiedItems.Add(simplifiedItem);
            }
            return simplifiedItems;
        }

        public Tuple<Wrap<T>, Wrap<T>> TrySimplifyItem<T>(Wrap<T> wrap)
        {
            var binExpr = GetExpr(wrap.Removable) as BinaryExpr;
            if (binExpr != null)
                if (binExpr.Op != BinaryExpr.Opcode.And) return null; //TODO simplify when theres an implies

            wrap.Remove();
            if (!_verifier.IsProgramValid(_program)) {
                return SimplifyItem(wrap);
            }
            Console.WriteLine("Whole assert can be completely removed separately"); //TODO figure out what to do here (remove from _removableItems?)
            return null;
        }

        private Tuple<Wrap<T>, Wrap<T>> SimplifyItem<T>(Wrap<T> wrap)
        {
            var brokenItemWraps = BreakAndReinsertItem(wrap);
            var itemRemoved = false;
            //Test to see which can be removed
            for (var assertNum = brokenItemWraps.Count - 1; assertNum >= 0; assertNum--) {
                var brokenItem = brokenItemWraps[assertNum];
                var brokenWrap = new Wrap<T>(brokenItem.Removable, wrap.ParentList);
                if (!_remover.TryRemove(brokenWrap)) continue;
                brokenItemWraps.Remove(brokenItem);
                itemRemoved = true;
            }

            //Remove the broken items from their parent
            foreach (var brokenItem in brokenItemWraps)
//                brokenItem.ParentList.Remove(brokenItem.Removable);
                brokenItem.Remove();

            //If nothing was removed, reinsert the original to its parent
            if (!itemRemoved) {
                wrap.Reinsert();
                return null;
            }

            var brokenItems = new List<T>();
            foreach (var brokenItemWrap in brokenItemWraps) {
                brokenItems.Add(brokenItemWrap.Removable);
            }
            var newExpr = CombineItems(brokenItems);

            //Create a new item
            var newItem = GetNewNodeFromItem(wrap.Removable, newExpr);
            //Insert the item
            wrap.ParentList.Insert(wrap.Index, newItem);
            //Wrap the new item
            var newWrap = new Wrap<T>(newItem, wrap.ParentList);

            //Test quickly
            var ver = new SimpleVerifier();
            if (!ver.IsProgramValid(_program)) throw new Exception("Failed to verify after combining items!");

            return new Tuple<Wrap<T>, Wrap<T>>(wrap, newWrap);
        }

        private List<Wrap<T>> BreakAndReinsertItem<T>(Wrap<T> wrap)
        {
            var brokenItems = BreakDownExpr(wrap);
            foreach (var brokenitem in brokenItems) {
                brokenitem.ParentList.Insert(wrap.Index, brokenitem.Removable);
            }
            return brokenItems;
        }

        private List<Wrap<T>> BreakDownExpr<T>(Wrap<T> wrap)
        {
            var brokenItems = new List<Wrap<T>>();
            var binaryExpr = GetExpr(wrap.Removable) as BinaryExpr;
            if (binaryExpr == null || binaryExpr.Op != BinaryExpr.Opcode.And) {
                brokenItems.Add(wrap);
                return brokenItems;
            }
            var newItem1 = GetNewNodeFromExpr(wrap, binaryExpr, binaryExpr.E0);
            var newItem2 = GetNewNodeFromExpr(wrap, binaryExpr, binaryExpr.E1);
            if (newItem1 != null) brokenItems.AddRange(BreakDownExpr(newItem1));
            if (newItem2 != null) brokenItems.AddRange(BreakDownExpr(newItem2));
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

        private Wrap<T> GetNewNodeFromExpr<T>(Wrap<T> originalWrap, BinaryExpr binExpr, Expression subExpr)
        {
            var assert = originalWrap.Removable as AssertStmt;
            if (assert != null) {
                return new Wrap<T>((T) (object) new AssertStmt(binExpr.tok, assert.EndTok, subExpr, assert.Attributes), originalWrap.ParentList);
            }
            var invariant = originalWrap.Removable as MaybeFreeExpression;
            if (invariant != null) {
                return new Wrap<T>((T) (object) new MaybeFreeExpression(subExpr), originalWrap.ParentList);
            }
            return null;
        }

        private Expression CombineItems<T>(List<T> brokenItems)
        {
            if (brokenItems.Count < 1)
                return null; //null
            if (brokenItems.Count == 1)
                return GetExpr(brokenItems[0]);

            var item = brokenItems[0];
            brokenItems.Remove(item);
            var left = GetExpr(item);
            var right = CombineItems(brokenItems);


            var binExpr = new BinaryExpr(left.tok, BinaryExpr.Opcode.And, left, right);
            return binExpr;
        }

        private T GetNewNodeFromItem<T>(T originalItem, Expression expr)
        {
            var assert = originalItem as AssertStmt;
            if (assert != null) {
                return (T) (object) new AssertStmt(assert.Tok, assert.EndTok, expr, assert.Attributes);
            }
            var invariant = originalItem as MaybeFreeExpression;
            if (invariant != null) {
                return (T) (object) new MaybeFreeExpression(expr);
            }
            throw new Exception("cant create a node from the item!");
        }
    }
}
