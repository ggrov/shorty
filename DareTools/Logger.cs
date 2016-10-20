using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;
using Microsoft.Dafny;
using Bpl = Microsoft.Boogie;
using Program = Microsoft.Dafny.Program;
using Dare;

namespace DareTools
{
    internal class Logger
    {
        public readonly List<Program> Programs;
        public readonly List<Program> InvalidPrograms = new List<Program>();
        private readonly int _numberOfTests;
        private readonly bool _runTimeTests;
        private readonly string _directory;
        private readonly List<LogData> _allLoggedData = new List<LogData>();

        public Logger(string directory, List<Program> programs, int numberOfTest, bool runTimeTests = true)
        {
            Contract.Requires(numberOfTest > 0);
            if (numberOfTest > 1 && !runTimeTests) 
                throw new Exception("not running time tests and having more than one testrun - there is no reason to ever do this");
            _directory = directory + "\\";
            _numberOfTests = numberOfTest;
            _runTimeTests = runTimeTests;
            Programs = programs;
            EnsureProgramsVerify();
        }

        private void EnsureProgramsVerify() {
            var totalCount = Programs.Count;
            for (var i = Programs.Count - 1; i >= 0; i--) {
                var program = Programs[i];
                Console.Write("\nChecking {0} | {1}/{2}", program.FullName, totalCount - i, totalCount);
                if (EnsureProgramVerifies(program)) {
                    continue;
                }
                InvalidPrograms.Add(program);
                Console.Write("  => Program {0} is not valid", program.Name);
                Programs.Remove(program);
            }
            Console.WriteLine("\n\nFound {0} invalid programs.  Running Logger on remaining {1} programs", totalCount - Programs.Count, Programs.Count);
        }

        private bool EnsureProgramVerifies(Program program)
        {
            try {
                return TryEnsureProgramVerifies(program);
            }
            catch {
                return false;
            }
        }

        private bool TryEnsureProgramVerifies(Program program)
        {
            var copy = SimpleCloner.CloneProgram(program);
            var dareController = new DareController(copy);
            return dareController.IsProgramValid();
        }

        private void WriteHeadings(TextWriter tw, string thing, bool isSimp)
        {
            tw.Write("Program Name, {0} Before, {0} After, {0} Removed, Removal Percentage", thing);
            if (isSimp)
                tw.WriteLine(", Remaining Items Simplified, Percentage of remaining items simplified, Subexpressions Before Simplification, Subexpressions After Simplification, Subexpressions Removed, Subexpression Removal Percentage");
            else
                tw.WriteLine();
        }

        public void LogAllData()
        {
            CheckValidityOfPrograms();
            var programNumber = 0;
            var fails = new Dictionary<Program, Exception>();
            foreach (var program in Programs) {
                try {
                    var logData = _runTimeTests ? new LogData(program, _numberOfTests) : new LogData(program);
                    Console.WriteLine("Getting data for {0} ({1}/{2})", program.Name, ++programNumber, Programs.Count);
                    logData.PerformLogging();
                    _allLoggedData.Add(logData);
                }
                catch (Exception e){
                    fails.Add(program, e);
                }
            }

            PrintFails(fails);

            LogFile("assert-removal", "Asserts", new AssertCounterFactory());
            LogFile("invariant-removal", "Invariants", new InvariantCounterFactory());
            LogFile("lemma-call-removal", "Lemma Calls", new LemmaCallCounterFactory());
            LogFile("decreases-removal", "Decreases", new DecreasesCounterFactory());
            LogFile("calc-removal", "Calcs", new CalcCounterFactory());
            LogFile("wildcard-removal", "Wildcard", new WildCardCounterFactory());
            LogSummaryData();
        }

        private void CheckValidityOfPrograms()
        {
            using (TextWriter tw = File.CreateText(_directory + "\\summary.txt")) {
                tw.WriteLine("Logging data for {0} programs out of an original {1}", Programs.Count, Programs.Count + InvalidPrograms.Count);
                if (InvalidPrograms.Count <= 0) return;
                tw.WriteLine("\nThe following {0} programs failed initial verification", InvalidPrograms.Count);
                foreach (var program in InvalidPrograms)
                    tw.WriteLine(program.FullName);
            }
        }

        private void PrintFails(Dictionary<Program, Exception> fails)
        {
            if (fails.Count <= 0) return;
            Console.WriteLine("\nThe following programs failed: ");
            using (TextWriter tw = File.CreateText(Path.Combine(_directory, "failed-programs.txt"))) {
                foreach (var failed in fails.Keys) {
                    try {
                        var msg = failed.Name + ": " + fails[failed].Message;
                        Console.WriteLine(msg);
                        tw.WriteLine(msg);
                    }
                    catch {
                        var msg = failed.Name + ": unable to print error...";
                        Console.WriteLine(msg);
                        tw.WriteLine(msg);
                    }
                }
            }
        }

        private void LogSummaryData()
        {
            var beforeAndAfterLineCounts = new Dictionary<LogData, Tuple<int, int>>();
            foreach (var logData in _allLoggedData) 
                beforeAndAfterLineCounts.Add(logData, logData.PrintBeforeAndAfter(_directory));

            using (TextWriter tw = File.CreateText(_directory + "\\summaryData.csv")) {
                tw.Write("Program name, loc before, loc after, loc removed");
                var totalLocBefore = 0;
                var totalLocAfter = 0;
                long totalVerTimeBefore = 0;
                long totalVerTimeAfter = 0;
                if(_runTimeTests)
                    tw.WriteLine(",Avg verification time before, Avg verification time after, Avg time improvement");
                else 
                    tw.WriteLine();
                foreach (var logData in _allLoggedData) {
                    var locBefore = beforeAndAfterLineCounts[logData].Item1;
                    var locAfter = beforeAndAfterLineCounts[logData].Item2;
                    totalLocBefore += locBefore;
                    totalLocAfter += locAfter;
                    tw.Write("{0},{1},{2},{3}", logData.OriginalProgram.Name, locBefore, locAfter, locBefore-locAfter);
                    if (_runTimeTests) {
                        tw.WriteLine(",{0},{1},{2}",logData.VerificationTimeBefore, logData.VerificationTimeAfter, logData.VerificationTimeBefore - logData.VerificationTimeAfter);
                        totalVerTimeBefore += logData.VerificationTimeBefore;
                        totalVerTimeAfter += logData.VerificationTimeAfter;
                    }
                    else
                        tw.WriteLine();
                }
                tw.WriteLine();
                tw.Write("Total,{0},{1},{2}",totalLocBefore, totalLocAfter, totalLocBefore-totalLocAfter);
                if (_runTimeTests)
                    tw.WriteLine(",{0},{1},{2}", totalVerTimeBefore, totalVerTimeAfter, totalVerTimeBefore - totalVerTimeAfter);
                else
                    tw.WriteLine();

                if (_allLoggedData.Count == 0) return;
                float avgLocBefore = (float) ((float) totalLocBefore/(float) _allLoggedData.Count);
                float avgLocAfter = (float) ((float) totalLocAfter/(float) _allLoggedData.Count);
                float avgLocRemoved = (float) ((float) totalLocBefore - totalLocAfter)/(float) _allLoggedData.Count;

                tw.Write("Average,{0},{1},{2}", avgLocBefore, avgLocAfter, avgLocRemoved);

                if (_runTimeTests) {
                    float avgVerTimeBefore = (float) ((float) totalVerTimeBefore/(float) _allLoggedData.Count);
                    float avgVerTimeAfter = (float) ((float) totalVerTimeAfter/(float) _allLoggedData.Count);
                    float avgVerTimeImprovement = (float) ((float) totalVerTimeBefore - totalVerTimeAfter)/(float) _allLoggedData.Count;

                    tw.WriteLine(",{0},{1},{2}", avgVerTimeBefore, avgVerTimeAfter, avgVerTimeImprovement);
                }
                else
                    tw.WriteLine();
            }
        }

        private void LogFile(string fileName, string itemsName, ICounterFactory counterFactory)
        {
            var fullFileName = _directory + fileName + ".csv";
            using (TextWriter tw = File.CreateText(fullFileName)) {
                bool isSimp = false;
                if (_allLoggedData.Count==0) return;

                if (counterFactory.GetNewCounter(_allLoggedData[0]) is SimpCounter)
                    isSimp = true;
                
                WriteHeadings(tw, itemsName, isSimp);

                var totalBefore = 0;
                var totalAfter = 0;
                var totalRemoved = 0;

                var totalSubexprsBefore = 0;
                var totalSubexprsAfter = 0;
                var totalNumItemsSimplified = 0;

                //var data = new List<Tuple<string, int, int, float, float, float>>();
                foreach (var logData in _allLoggedData) {
                    var counter = counterFactory.GetNewCounter(logData);
                    var countBefore = counter.GetCountBefore();
                    if(countBefore == 0) continue;
                    var countAfter = counter.GetCountAfter();
                    var countRemoved = counter.GetRemovedCount();
                    float removalPercentage = ((float) countRemoved/(float) countBefore) * 100;
                    totalBefore += countBefore;
                    totalAfter += countAfter;
                    totalRemoved += countRemoved;

                    tw.Write("{0},{1},{2},{3},{4}%",logData.OriginalProgram.Name, countBefore, countAfter, countRemoved, removalPercentage);
                    if (!isSimp || countAfter == 0) {
                        tw.WriteLine();
                    }
                    else {
                        var simpCounter = counter as SimpCounter;
                        var numberOfItemsSimplified = simpCounter.GetNumberOfRemainingThatCanBeSimplified();
                        var subexprsBeforeSimplification = simpCounter.GetNumberOfSubexpressionsBeforeSimplification();
                        var subexprsAfterSimplification = simpCounter.GetNumberOfSubexpressionsAfterSimplification();
                        var subexprsRemoved = subexprsBeforeSimplification - subexprsAfterSimplification;
                        totalNumItemsSimplified += numberOfItemsSimplified;
                        totalSubexprsBefore += subexprsBeforeSimplification;
                        totalSubexprsAfter += subexprsAfterSimplification;
                        float subexprRemovedPercentage = ((float) subexprsRemoved/(float) subexprsBeforeSimplification) * 100f;
                        float numberRemainingItemsSimplified = ((float)numberOfItemsSimplified/(float)countAfter)*100f;
                        tw.WriteLine(",{0},{1}%,{2},{3},{4},{5}%",numberOfItemsSimplified, numberRemainingItemsSimplified, subexprsBeforeSimplification, subexprsAfterSimplification,
                            subexprsRemoved, subexprRemovedPercentage);
                    }
                }
                tw.WriteLine();
                float avgRemovalPct = ((float)totalRemoved/(float)totalBefore)*100f;
                tw.Write("Total,{0},{1},{2},{3}%", totalBefore, totalAfter, totalRemoved, avgRemovalPct);
                if (!isSimp || totalAfter == 0)
                    tw.WriteLine();
                else {
                    var subExprsRemoved = totalSubexprsBefore - totalSubexprsAfter;
                    float subExprRemovalPct = ((float)subExprsRemoved/(float)totalSubexprsBefore)*100f;
                    float pctOfRemainingSimplified = ((float) totalNumItemsSimplified/(float) totalAfter)*100f;
                    tw.WriteLine(",{0},{1}%,{2},{3},{4},{5}%",totalNumItemsSimplified, pctOfRemainingSimplified,
                        totalSubexprsBefore, totalSubexprsAfter, subExprsRemoved, subExprRemovalPct);
                }
            }
        }
    }

    class LogData
    {
        public Program OriginalProgram { get; private set; }
        public Program ModifiedProgram { get; private set; }

        public DareController OriginalDareController { get; private set; }
        public DareController ModifiedDareController { get; private set; }

        public SimplificationData SimpData { get; private set; }

        public long VerificationTimeBefore { get; private set; }
        public long VerificationTimeAfter { get; private set; }


        private readonly int _numberOfVerifications = 0;

        public LogData(Program program)
        {
            OriginalProgram = SimpleCloner.CloneProgram(program);
        }

        public LogData(Program program, int numberOfVerifications)
        {
            _numberOfVerifications = numberOfVerifications;
            OriginalProgram = SimpleCloner.CloneProgram(program);
        }

        public Tuple<int,int> PrintBeforeAndAfter(string directory)
        {
            var plainFileName = OriginalProgram.Name.Substring(0, OriginalProgram.Name.Length - 4);
            var directoryName = directory + "\\generatedPrograms\\" + plainFileName;
            Directory.CreateDirectory(directoryName);

            var beforeFileName = directoryName + "\\" + plainFileName + "-before.dfy";
            var afterFileName = directoryName + "\\" + plainFileName + "-after.dfy";

            //try {
                using (TextWriter tw = File.CreateText(beforeFileName))
                    OriginalDareController.PrintProgram(tw);

                using (TextWriter tw = File.CreateText(afterFileName))
                    ModifiedDareController.PrintProgram(tw);
//            }
//            catch {
//                Console.WriteLine("Unable to print "+ OriginalProgram.Name);
//            }
            var lineCountBefore = File.ReadLines(beforeFileName).Count();
            var lineCountAfter = File.ReadLines(afterFileName).Count();

            return new Tuple<int, int>(lineCountBefore, lineCountAfter);
        }

        public void PerformLogging()
        {
            GetVerificationTimeBefore();
            OriginalDareController = new DareController(OriginalProgram); //this is for counting later...
            ModifiedProgram = SimpleCloner.CloneProgram(OriginalProgram);
            ModifiedDareController = new DareController(ModifiedProgram);
            SimpData = ModifiedDareController.FastRemoveAllRemovables();
            GetVerificationTimeAfter();
        }

        private void GetVerificationTimeBefore()
        {
            if (_numberOfVerifications < 1) return;
            VerificationTimeBefore = GetAverageVerificationTime(OriginalProgram);
        }
        private void GetVerificationTimeAfter()
        {
            if (_numberOfVerifications < 1) return;
            VerificationTimeAfter = GetAverageVerificationTime(ModifiedProgram);
        }

        private long GetAverageVerificationTime(Program program)
        {
            long verificationTime = 0;
            for (var i = 0; i < _numberOfVerifications; i++) {
                verificationTime += GetVerificationTime(program);
            }
            return verificationTime/_numberOfVerifications;
        }

        private long GetVerificationTime(Program program)
        {
            var verifier = new SimpleVerifier();
            var sw = new Stopwatch();
            var origSnapshotSetting = DafnyOptions.O.VerifySnapshots;
            DafnyOptions.O.VerifySnapshots = 0;
            var programClone = SimpleCloner.CloneProgram(program);
            sw.Start();
            verifier.IsProgramValid(programClone);
            sw.Stop();
            DafnyOptions.O.VerifySnapshots = origSnapshotSetting;
            return sw.ElapsedMilliseconds;
        }
    }

    #region Counters
    
    internal abstract class Counter {
        
        protected LogData LogData;

        protected Counter(LogData logData)
        {
            LogData = logData;
        }

        public abstract int GetCountBefore();
        public abstract int GetCountAfter();
        public abstract int GetRemovedCount();
    }

    internal abstract class SimpCounter : Counter
    {
        protected SimpCounter(LogData logData) : base(logData) {}
        public abstract int GetNumberOfRemainingThatCanBeSimplified();
        public abstract int GetNumberOfSubexpressionsBeforeSimplification();
        public abstract int GetNumberOfSubexpressionsAfterSimplification();
        protected int CountExpr(Expression expr)
        {
            var binExpr = expr as BinaryExpr;
            if (binExpr == null || binExpr.Op != BinaryExpr.Opcode.And) return 1;
            return CountExpr(binExpr.E0) + CountExpr(binExpr.E1);
        }
    }

    internal class AssertCounter : SimpCounter
    {
        public AssertCounter(LogData logData) : base(logData) {}

        public override int GetCountBefore()
        {
            return LogData.OriginalDareController.Asserts.Count;
        }

        public override int GetCountAfter()
        {
            return LogData.ModifiedDareController.Asserts.Count;
        }

        public override int GetRemovedCount()
        {
            return LogData.SimpData.RemovableAsserts.Count;
        }

        public override int GetNumberOfRemainingThatCanBeSimplified()
        {
            return LogData.SimpData.SimplifiedAsserts.Count;
        }

        public override int GetNumberOfSubexpressionsBeforeSimplification()
        {
            var amount = 0;
            //As the final results will have already simplified, we count all the removed
            //subexpressions then subtract that from the total original subexpressions
            var dareControllerOriginal = LogData.OriginalDareController;

            //unwrap the original asserts
            var allOriginalAsserts = new List<AssertStmt>();
            foreach (var assertWrap in dareControllerOriginal.Asserts) {
                allOriginalAsserts.Add(assertWrap.Removable as AssertStmt);
            }

            var totalSubExprsCount = CountSubexpressions(allOriginalAsserts);
            var removedSubExprsCount = CountSubexpressions(LogData.SimpData.RemovableAsserts);

            amount = totalSubExprsCount - removedSubExprsCount;
            return amount;
        }

        private int CountSubexpressions(List<AssertStmt> allOriginalAsserts)
        {
            var amount = 0;
            foreach (var assert in allOriginalAsserts)
                amount += CountExpr(assert.Expr);
            return amount;
        }

        public override int GetNumberOfSubexpressionsAfterSimplification()
        {
            var amountRemoved = 0;
            var total = GetNumberOfSubexpressionsBeforeSimplification();
            foreach (var tup in LogData.SimpData.SimplifiedAsserts)
                amountRemoved += CountExpr((tup.Item1 as AssertStmt).Expr) - CountExpr((tup.Item2 as AssertStmt).Expr);
            return total - amountRemoved;
        }
    }

    class InvariantCounter : SimpCounter
    {
        public InvariantCounter(LogData logData) : base(logData) {}

        public override int GetCountBefore()
        {
            return LogData.OriginalDareController.Invariants.Count;
        }

        public override int GetCountAfter()
        {
            return LogData.ModifiedDareController.Invariants.Count;
        }

        public override int GetRemovedCount()
        {
            return LogData.SimpData.RemovableInvariants.Count;
        }

        public override int GetNumberOfRemainingThatCanBeSimplified()
        {
            return LogData.SimpData.SimplifiedInvariants.Count;
        }

        public override int GetNumberOfSubexpressionsBeforeSimplification()
        {
            var amount = 0;
            var dareControllerOriginal = LogData.OriginalDareController;

            var allOriginalInvariants = new List<MaybeFreeExpression>();
            foreach (var invariantWrap in dareControllerOriginal.Invariants) {
                allOriginalInvariants.Add(invariantWrap.Removable);
            }

            var totalSubExprsCount = CountSubexpressions(allOriginalInvariants);
            var removedSubExprsCount = CountSubexpressions(LogData.SimpData.RemovableInvariants);

            amount = totalSubExprsCount - removedSubExprsCount;
            return amount;
        }

        private int CountSubexpressions(List<MaybeFreeExpression> allOriginalInvariants)
        {
            var amount = 0;
            foreach (var invariant in allOriginalInvariants)
                amount += CountExpr(invariant.E);
            return amount;
        }

        public override int GetNumberOfSubexpressionsAfterSimplification()
        {
            var amountRemoved = 0;
            var total = GetNumberOfSubexpressionsBeforeSimplification();
            foreach (var tup in LogData.SimpData.SimplifiedInvariants) 
                amountRemoved += CountExpr(tup.Item1.E) - CountExpr(tup.Item2.E);
            return total - amountRemoved;
        }
    }

    class DecreasesCounter : Counter
    {
        public DecreasesCounter(LogData logData) : base(logData) {}

        public override int GetCountBefore()
        {
            return LogData.OriginalDareController.Decreases.Count;
        }

        public override int GetCountAfter()
        {
            return LogData.ModifiedDareController.Decreases.Count;
        }

        public override int GetRemovedCount()
        {
            //return LogData.SimpData.RemovableDecreases.Count; -- think this includes wildcards
            return GetCountBefore() - GetCountAfter();
        }
    }

    class LemmaCallCounter : Counter
    {
        public override int GetCountBefore()
        {
            return LogData.OriginalDareController.LemmaCalls.Count;
        }

        public override int GetCountAfter()
        {
            return LogData.ModifiedDareController.LemmaCalls.Count;
        }

        public override int GetRemovedCount()
        {
            return LogData.SimpData.RemovableLemmaCalls.Count;
        }

        public LemmaCallCounter(LogData logData) : base(logData) {}
    }

    internal class CalcStatementCounter : SimpCounter
    {
        public CalcStatementCounter(LogData logData) : base(logData) {}

        public override int GetCountBefore()
        {
            return LogData.OriginalDareController.Calcs.Count;
        }

        public override int GetCountAfter()
        {
            return LogData.ModifiedDareController.Calcs.Count;
        }

        public override int GetRemovedCount()
        {
            return LogData.SimpData.RemovableCalcs.Count;
        }

        public override int GetNumberOfRemainingThatCanBeSimplified()
        {
            var remaining = GetCountAfter();
            return LogData.SimpData.SimplifiedCalcs.Item4.Count ; 
        }

        public override int GetNumberOfSubexpressionsBeforeSimplification()
        {
            //this is found by total subexpressions - removed subexpressions
            var originalDareController = LogData.OriginalDareController;
            var calcs = new List<CalcStmt>();
            foreach (var wrap in originalDareController.Calcs) {
                calcs.Add(wrap.Removable as CalcStmt);
            }
            var originalSubexprsCount = CountCalcParts(calcs);

            return originalSubexprsCount - CountCalcParts(LogData.SimpData.RemovableCalcs);

        }

        public override int GetNumberOfSubexpressionsAfterSimplification()
        {
            var dareController = LogData.ModifiedDareController;
            var calcs = new List<CalcStmt>();
            foreach (var wrap in dareController.Calcs)
                calcs.Add(wrap.Removable as CalcStmt);
            return CountCalcParts(calcs);
        }

        private int CountCalcParts(List<CalcStmt> calcs)
        {
            var calcPartCount = 0;
            foreach (var calcStmt in calcs) {
                calcPartCount += calcStmt.Hints.Count(hint => hint.Body.Count > 0);
                calcPartCount += calcStmt.Lines.Count - 1; // -1 because of the dummy
            }
            return calcPartCount;
        }
    }

    class WildCardCounter : Counter
    {
        public WildCardCounter(LogData logData) : base(logData) {}
        public override int GetCountBefore() {
            var count = 0;
            foreach (var wildCard in LogData.OriginalDareController.AllRemovableTypes.WildCardDecreaseses) {
                count += wildCard.Count;
            }
            return count;
        }

        private int CountWildCards(WildCardDecreases wildCard) {
            var count = 1; //1 is THIS wildcard
            foreach (var subWildCard in wildCard.SubDecreases) {
                count += CountWildCards(subWildCard);
            }
            return count;
        }

        public override int GetCountAfter() { //Not sure if tree is changed....
            var count = 0;
            foreach (var wildCard in LogData.OriginalDareController.AllRemovableTypes.WildCardDecreaseses) {
                count += CountWildCards(wildCard);
            }
            return count;
        }

        public override int GetRemovedCount() {
            return GetCountBefore() - GetCountAfter();
        }
    }

    #endregion

    #region Counter Factories

    interface ICounterFactory
    {
        Counter GetNewCounter(LogData logData);
    }

    class AssertCounterFactory : ICounterFactory
    {
        public Counter GetNewCounter(LogData logData)
        {
            return new AssertCounter(logData);
        }
    }

    class InvariantCounterFactory : ICounterFactory
    {
        public Counter GetNewCounter(LogData logData)
        {
            return new InvariantCounter(logData);
        }
    }

    class DecreasesCounterFactory : ICounterFactory
    {
        public Counter GetNewCounter(LogData logData)
        {
            return new DecreasesCounter(logData);
        }
    }
    class LemmaCallCounterFactory : ICounterFactory
    {
        public Counter GetNewCounter(LogData logData)
        {
            return new LemmaCallCounter(logData);
        }
    }
    class CalcCounterFactory : ICounterFactory
    {
        public Counter GetNewCounter(LogData logData)
        {
            return new CalcStatementCounter(logData);
        }
    }

    class WildCardCounterFactory : ICounterFactory
    {
        public Counter GetNewCounter(LogData logData) {
            return new WildCardCounter(logData);
        }
    }

    #endregion

}
