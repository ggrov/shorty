using System;
using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;
using Microsoft.Dafny;
using Bpl = Microsoft.Boogie;
using Program = Microsoft.Dafny.Program;
using Dary;
using Dary = Dary.Dary;

namespace DaryTools
{
    //TODO: update to use SimultaneousAllTypeRemover
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
            if (numberOfTest > 1 && !runTimeTests) {
                throw new Exception("not running time tests and having more than one testrun - there is literally no reason to ever do this");
            }
            _directory = directory + "\\";
            _numberOfTests = numberOfTest;
            _runTimeTests = runTimeTests;
            Programs = programs;
            EnsureProgramsVerify();
        }

        private void EnsureProgramsVerify()
        {
            for (var i = Programs.Count - 1; i >= 0; i--) {
                var program = Programs[i];
                if (EnsureProgramVerifies(program)) continue;
                InvalidPrograms.Add(program);
                Console.WriteLine("  => Program {0} is not valid", program.Name);
                Programs.Remove(program);
            }
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
            Console.WriteLine("Checking " + program.FullName);
            var copy = SimpleCloner.CloneProgram(program);
            var daryController = new DaryController(copy);
            return daryController.IsProgramValid();
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
            using (TextWriter tw = File.CreateText(_directory + "\\summary.txt")) {
                tw.WriteLine("Logging data for {0} programs", Programs.Count);
                if (InvalidPrograms.Count > 0) {
                    tw.WriteLine("\nThe following programs failed initial verification");
                    foreach (var program in InvalidPrograms)
                        tw.WriteLine(program.FullName);
                }
            }

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

            Console.WriteLine("\nThe following programs failed: ");
            foreach (var failed in fails.Keys) {
                try {
                    Console.WriteLine(failed.Name + ": " + fails[failed].Message);
                }
                catch {
                    Console.WriteLine(failed.Name + ": unable to print error...");
                }
            }
            
            LogFile("assert-removal", "Asserts", new AssertCounterFactory());
            LogFile("invariant-removal", "Invariants", new InvariantCounterFactory());
            LogFile("lemma-call-removal", "Lemma Calls", new LemmaCallCounterFactory());
            LogFile("decreases-removal", "Decreases", new DecreasesCounterFactory());
            LogFile("calc-removal", "Calcs", new CalcCounterFactory());
            LogSummaryData();
        }

        private void LogSummaryData()
        {
            var beforeAndAfterLineCounts = new Dictionary<LogData, Tuple<int, int>>();
            foreach (var logData in _allLoggedData) 
                beforeAndAfterLineCounts.Add(logData, logData.PrintBeforeAndAfter(_directory));

            using (TextWriter tw = File.CreateText(_directory + "\\summartData.csv")) {
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
                        tw.WriteLine("{0},{1},{2}",logData.VerificationTimeBefore, logData.VerificationTimeAfter, logData.VerificationTimeBefore - logData.VerificationTimeAfter);
                        totalVerTimeBefore += logData.VerificationTimeBefore;
                        totalVerTimeAfter += logData.VerificationTimeAfter;
                    }
                    else
                        tw.WriteLine();
                }
                tw.WriteLine();
                tw.Write("Total,{0},{1},{2}",totalLocBefore, totalLocAfter, totalLocBefore-totalLocAfter);
                if (_runTimeTests)
                    tw.WriteLine("{0},{1},{2}", totalVerTimeBefore, totalVerTimeAfter, totalVerTimeBefore - totalVerTimeAfter);
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

                    tw.WriteLine("{0},{1},{2}", avgVerTimeBefore, avgVerTimeAfter, avgVerTimeImprovement);
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
                        var subexprsBeforeSimplification = simpCounter.GetNumberOfSubexpressionsAfterRemoval();
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

        public DaryController OriginalDaryController { get; private set; }
        public DaryController ModifiedDaryController { get; private set; }

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

            try {
                using (TextWriter tw = File.CreateText(beforeFileName))
                    OriginalDaryController.PrintProgram(tw);

                using (TextWriter tw = File.CreateText(afterFileName))
                    ModifiedDaryController.PrintProgram(tw);
            }
            catch {
                Console.WriteLine("Unable to print "+ OriginalProgram.Name);
            }
            var lineCountBefore = File.ReadLines(beforeFileName).Count();
            var lineCountAfter = File.ReadLines(afterFileName).Count();

            return new Tuple<int, int>(lineCountBefore, lineCountAfter);
        }

        public void PerformLogging()
        {
            GetVerificationTimeBefore();
            OriginalDaryController = new DaryController(OriginalProgram); //this is for counting later...
            ModifiedProgram = SimpleCloner.CloneProgram(OriginalProgram);
            ModifiedDaryController = new DaryController(ModifiedProgram);
            SimpData = ModifiedDaryController.FastRemoveAllRemovables();
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
            sw.Start();
            verifier.IsProgramValid(program);
            sw.Stop();
            DafnyOptions.O.VerifySnapshots = origSnapshotSetting;
            return sw.ElapsedMilliseconds;
        }
    }

    #region Counters
    
    internal abstract class Counter {
        
        protected LogData logData;

        public Counter(LogData logData)
        {
            this.logData = logData;
        }

        public abstract int GetCountBefore();
        public abstract int GetCountAfter();
        public abstract int GetRemovedCount();
    }

    internal abstract class SimpCounter : Counter
    {
        protected SimpCounter(LogData logData) : base(logData) {}
        public abstract int GetNumberOfRemainingThatCanBeSimplified();
        public abstract int GetNumberOfSubexpressionsAfterRemoval();
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
            return logData.OriginalDaryController.Asserts.Count;
        }

        public override int GetCountAfter()
        {
            return logData.ModifiedDaryController.Asserts.Count;
        }

        public override int GetRemovedCount()
        {
            return logData.SimpData.RemovableAsserts.Count;
        }

        public override int GetNumberOfRemainingThatCanBeSimplified()
        {
            return logData.SimpData.SimplifiedAsserts.Count;
        }

        public override int GetNumberOfSubexpressionsAfterRemoval()
        {
            var amount = 0;
            //As the final results will have already simplified, we count all the removed
            //subexpressions then subtract that from the total original subexpressions
            var daryControllerOriginal = logData.OriginalDaryController;

            //unwrap the original asserts
            var allOriginalAsserts = new List<AssertStmt>();
            foreach (var assertWrap in daryControllerOriginal.Asserts) {
                allOriginalAsserts.Add(assertWrap.Removable as AssertStmt);
            }

            var totalSubExprsCount = CountSubexpressions(allOriginalAsserts);
            var removedSubExprsCount = CountSubexpressions(logData.SimpData.RemovableAsserts);

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
            var total = GetNumberOfSubexpressionsAfterRemoval();
            foreach (var tup in logData.SimpData.SimplifiedAsserts)
                amountRemoved += CountExpr((tup.Item1 as AssertStmt).Expr) - CountExpr((tup.Item2 as AssertStmt).Expr);
            return total - amountRemoved;
        }
    }

    class InvariantCounter : SimpCounter
    {
        public InvariantCounter(LogData logData) : base(logData) {}

        public override int GetCountBefore()
        {
            return logData.OriginalDaryController.Invariants.Count;
        }

        public override int GetCountAfter()
        {
            return logData.ModifiedDaryController.Invariants.Count;
        }

        public override int GetRemovedCount()
        {
            return logData.SimpData.RemovableInvariants.Count;
        }

        public override int GetNumberOfRemainingThatCanBeSimplified()
        {
            return logData.SimpData.SimplifiedInvariants.Count;
        }

        public override int GetNumberOfSubexpressionsAfterRemoval()
        {
            var amount = 0;
            var daryControllerOriginal = logData.OriginalDaryController;

            var allOriginalInvariants = new List<MaybeFreeExpression>();
            foreach (var invariantWrap in daryControllerOriginal.Invariants) {
                allOriginalInvariants.Add(invariantWrap.Removable);
            }

            var totalSubExprsCount = CountSubexpressions(allOriginalInvariants);
            var removedSubExprsCount = CountSubexpressions(logData.SimpData.RemovableInvariants);

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
            var total = GetNumberOfSubexpressionsAfterRemoval();
            foreach (var tup in logData.SimpData.SimplifiedInvariants) 
                amountRemoved += CountExpr(tup.Item1.E) - CountExpr(tup.Item2.E);
            return total - amountRemoved;
        }
    }

    class DecreasesCounter : Counter
    {
        public DecreasesCounter(LogData logData) : base(logData) {}

        public override int GetCountBefore()
        {
            return logData.OriginalDaryController.Decreases.Count;
        }

        public override int GetCountAfter()
        {
            return logData.ModifiedDaryController.Decreases.Count;
        }

        public override int GetRemovedCount()
        {
            return logData.SimpData.RemovableDecreases.Count;
        }
    }

    class LemmaCallCounter : Counter
    {
        public override int GetCountBefore()
        {
            return logData.OriginalDaryController.LemmaCalls.Count;
        }

        public override int GetCountAfter()
        {
            return logData.ModifiedDaryController.LemmaCalls.Count;
        }

        public override int GetRemovedCount()
        {
            return logData.SimpData.RemovableLemmaCalls.Count;
        }

        public LemmaCallCounter(LogData logData) : base(logData) {}
    }

    internal class CalcStatementCounter : SimpCounter
    {
        public CalcStatementCounter(LogData logData) : base(logData) {}

        public override int GetCountBefore()
        {
            return logData.OriginalDaryController.Calcs.Count;
        }

        public override int GetCountAfter()
        {
            return logData.ModifiedDaryController.Calcs.Count;
        }

        public override int GetRemovedCount()
        {
            return logData.SimpData.RemovableCalcs.Count;
        }

        public override int GetNumberOfRemainingThatCanBeSimplified()
        {
            var remaining = GetCountAfter();
            return logData.SimpData.SimplifiedCalcs.Item4.Count ; 
        }

        public override int GetNumberOfSubexpressionsAfterRemoval()
        {
            //this is found by total subexpressions - removed subexpressions
            var originalDaryController = logData.OriginalDaryController;
            var calcs = new List<CalcStmt>();
            foreach (var wrap in originalDaryController.Calcs) {
                calcs.Add(wrap.Removable as CalcStmt);
            }
            var originalSubexprsCount = CountCalcParts(calcs);

            return originalSubexprsCount - CountCalcParts(logData.SimpData.RemovableCalcs);

        }

        public override int GetNumberOfSubexpressionsAfterSimplification()
        {
            var daryController = logData.ModifiedDaryController;
            var calcs = new List<CalcStmt>();
            foreach (var wrap in daryController.Calcs)
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

    #endregion

}
