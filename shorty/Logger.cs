using System;
using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.Diagnostics;
using System.IO;
using System.Diagnostics.Contracts;
using System.Linq;
using Microsoft.Dafny;
using Bpl = Microsoft.Boogie;

namespace shorty
{
    class Logger
    {
        public readonly List<Program> Programs;
        public readonly List<Program> InvalidPrograms = new List<Program>();
        private readonly int _numberOfTests;
        private readonly bool _runTimeTests;
        private readonly string _directory;

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
            var copy = CloneProgram(program);
            var shorty = new Shorty(copy);
            return shorty.IsProgramValid();
        }

        private Program CloneProgram(Program program)
        {
            var cloner = new Cloner();
            var moduleDecl = new LiteralModuleDecl(cloner.CloneModuleDefinition(program.DefaultModuleDef, program.Name), null);
            return new Program(program.FullName, moduleDecl, program.BuiltIns, new InvisibleErrorReporter());
        }

        private void WriteHeadings(TextWriter tw, string thing)
        {
            tw.Write("Program Name, {0} Before, {0} After, {0} Removed, Removal Percentage", thing);
            if (_runTimeTests)
                tw.WriteLine(", Avg Execution Time(ms), Avg Verification Time Before, Avg Verification Time After, Avg Verification Time Improvement");
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

//            LogFile("assert-removal", "Asserts", new AssertLogFinderFactory());
//            LogFile("assert-simplification","Assert Subexpressions", new AssertSimpLogFinderFactory());
//            LogFile("invariant-removal", "Invariants", new InvariantLogFinderFactory());
//            LogFile("invariant-simplification","Invariant Subexpressions", new InvariantSimpLogFinderFactory());
            LogFile("lemma-call-removal", "Lemma Calls", new LemmaCallLogFinderFactory());
//            LogFile("decreases-removal", "Decreases", new DecreasesLogFinderFactory());
//            LogFile("calc-removal", "Calc Parts", new CalcLogFinderFactory());
        }

        private void LogFile(string fileName, string itemsName, ILogFinderFactory logFinderFactory)
        {
            string fullFileName = _directory + fileName + ".csv";
            using (TextWriter tw = File.CreateText(fullFileName))
            {
                WriteHeadings(tw, itemsName);
                int count = 1;
                var data = new List<Tuple<string, int, int, float, float, float>>();
                foreach (var program in Programs)
                {
                    var logFinder = logFinderFactory.GetLogFinder(program, _numberOfTests, _runTimeTests);
                    try
                    {
                        Console.WriteLine("Removing {3} from {0}: {1}/{2} ", program.Name, count++, Programs.Count, itemsName.ToLower());
                        data.Add(logFinder.GetLogData());
                    }
                    catch (Exception e)
                    {
                        tw.WriteLine("{0}, FAILED", program.Name);
                        Console.WriteLine("  => Failed to remove {2} from {0}: {1}", program.Name, e.Message, itemsName.ToLower());
                    }
                }

                LogTupleListData(data, tw);
            }
        }

        private void LogTupleListData(List<Tuple<string, int, int, float, float, float>> data, TextWriter tw)
        {
            var totalBefore = 0;
            var totalRemoved = 0;
            var totalAfter = 0;
            float totalTime = 0;
            float totalVerTimeBefore = 0;
            float totalVerTimeAfter = 0;

            foreach (var tuple in data) {
                var name = tuple.Item1;
                var before = tuple.Item2;
                var after = tuple.Item3;
                var removed = before - after;
                var percentage = 100f - ((float) after/(float) before)*100f;
                totalBefore += before;
                totalRemoved += removed;
                totalAfter += after;
                if (_runTimeTests) {
                    var executionTime = tuple.Item4;
                    var verTimeBefore = tuple.Item5;
                    var verTimeAfter = tuple.Item6;
                    var verTimeImprovement = verTimeBefore - verTimeAfter;
                    tw.WriteLine("{0}, {1}, {2}, {3}, {4}, {5}, {6}, {7}, {8}", name, before, after, removed, percentage + "%", executionTime, verTimeBefore, verTimeAfter, verTimeImprovement);
                    totalTime += executionTime;
                    totalVerTimeBefore += verTimeBefore;
                    totalVerTimeAfter += verTimeAfter;
                }
                else
                    tw.WriteLine("{0}, {1}, {2}, {3}, {4}", name, before, after, removed, percentage + "%");
            }

            var overAllPercentage = 100f - ((float) totalAfter/(float) totalBefore)*100;
            if (_runTimeTests) {
                var totalVerTimeImprovement = totalVerTimeBefore - totalVerTimeAfter;
                tw.WriteLine("Total, {0}, {1}, {2}, {3}, {4}, {5}, {6}, {7}", totalBefore, totalAfter, totalRemoved, overAllPercentage + "%", totalTime, totalVerTimeBefore, totalVerTimeAfter, totalVerTimeImprovement);
                tw.WriteLine(",,,,,,,Avg ver Time Improvement:,{0}", totalVerTimeImprovement/Programs.Count);
            }
            else
                tw.WriteLine("Total, {0}, {1}, {2}, {3}", totalBefore, totalAfter, totalRemoved, overAllPercentage + "%");
        }
    }

    #region LogFinder Factories

    public interface ILogFinderFactory
    {
        LogFinder GetLogFinder(Program program, int numberOfTests, bool runTimeTests);
    }

    class AssertLogFinderFactory : ILogFinderFactory
    {
        public LogFinder GetLogFinder(Program program, int numberOfTests, bool runTimeTests)
        {
            return new AssertLogFinder(program, numberOfTests, runTimeTests);
        }
    }

    class AssertSimpLogFinderFactory : ILogFinderFactory
    {
        public LogFinder GetLogFinder(Program program, int numberOfTests, bool runTimeTests)
        {
            return new AssertSimpLogFinder(program, numberOfTests, runTimeTests);
        }
    }

    class InvariantLogFinderFactory : ILogFinderFactory
    {
        public LogFinder GetLogFinder(Program program, int numberOfTests, bool runTimeTests)
        {
            return new InvariantLogFinder(program, numberOfTests, runTimeTests);
        }
    }

    class InvariantSimpLogFinderFactory : ILogFinderFactory
    {
        public LogFinder GetLogFinder(Program program, int numberOfTests, bool runTimeTests)
        {
            return new InvariantSimpLogFinder(program, numberOfTests, runTimeTests);
        }
    }

    class LemmaCallLogFinderFactory: ILogFinderFactory
    {
        public LogFinder GetLogFinder(Program program, int numberOfTests, bool runTimeTests)
        {
            return new LemmaCallLogFinder(program, numberOfTests, runTimeTests);
        }
    }

    class DecreasesLogFinderFactory : ILogFinderFactory
    {
        public LogFinder GetLogFinder(Program program, int numberOfTests, bool runTimeTests)
        {
            return new DecreasesLogFinder(program, numberOfTests, runTimeTests);
        }
    }

    class CalcLogFinderFactory : ILogFinderFactory
    {
        public LogFinder GetLogFinder(Program program, int numberOfTests, bool runTimeTests)
        {
            return new CalcLogFinder(program, numberOfTests, runTimeTests);
        }
    }


    #endregion

    #region LogFinders

    public abstract class LogFinder
    {
        protected Program Program;
        private readonly int _numberOfTests;
        private bool _runTimeTests;

        protected LogFinder(Program program, int numberOfTests, bool runTimeTest)
        {
            Program = program;
            _numberOfTests = numberOfTests;
            _runTimeTests = runTimeTest;
        }

        public Tuple<string, int, int, float, float, float> GetLogData()
        {
            float averageExecutionTime = 0;
            float averageTimeBefore = 0;
            float averageTimeAfter = 0;

            var initResults = RunInitialTest();
            var countBefore = initResults.Item4;
            var countAfter = initResults.Item5;

            if (_runTimeTests) {
                averageExecutionTime += initResults.Item1;
                averageTimeBefore += initResults.Item2;
                averageTimeAfter += initResults.Item3;
            }
            for (var i = 0; i < _numberOfTests - 1; i++) {
                var programClone = SimpleCloner.CloneProgram(Program);
                var shorty = new Shorty(programClone);
                var runData = RunTest(shorty);
                if (!_runTimeTests) continue;
                averageExecutionTime += runData.Item1;
                averageTimeBefore += runData.Item2;
                averageTimeAfter += runData.Item3;
            }
            if (_runTimeTests) {
                averageExecutionTime /= _numberOfTests;
                averageTimeBefore /= _numberOfTests;
                averageTimeAfter /= _numberOfTests;
            }
            return new Tuple<string, int, int, float, float, float>(Program.Name, countBefore, countAfter, averageExecutionTime, averageTimeBefore, averageTimeAfter);
        }

        private Tuple<long, long, long, int, int> RunInitialTest()
        {
            var programClone = SimpleCloner.CloneProgram(Program);
            var shorty = new Shorty(programClone);
            var countBefore = GetCount(shorty);
            var data = new Tuple<long, long, long>(0, 0, 0);
            if (_runTimeTests)
                data = RunTest(shorty);
            else
                GetRemovedItemsCount(shorty);
            var countAfter = GetCount(shorty);
            return new Tuple<long, long, long, int, int>(data.Item1, data.Item2, data.Item3, countBefore, countAfter);
        }

        /// <summary>
        /// </summary>
        /// <returns>A tuple containing the execution time, the verification time before and the verification time after</returns>
        private Tuple<long, long, long> RunTest(Shorty shorty)
        {
            var shortyExecutionTimeStopwatch = new Stopwatch();
            var verificationTimeBefore = GetVerificationTime(shorty);
            shortyExecutionTimeStopwatch.Start();
            GetRemovedItemsCount(shorty);
            shortyExecutionTimeStopwatch.Stop();
            var verificationTimeAfter = GetVerificationTime(shorty);
            return new Tuple<long, long, long>(shortyExecutionTimeStopwatch.ElapsedMilliseconds, verificationTimeBefore, verificationTimeAfter);
        }

        private long GetVerificationTime(Shorty shorty)
        {
            Bpl.CommandLineOptions.Clo.VerifySnapshots = 0;
            var watch = new Stopwatch();
            watch.Start();
            if (!shorty.IsProgramValid())
                throw new Exception("Cannot find verification time as program is not valid!");
            watch.Stop();
            Bpl.CommandLineOptions.Clo.VerifySnapshots = 1;
            return watch.ElapsedMilliseconds;
        }

        public abstract int GetRemovedItemsCount(Shorty shorty);

        public abstract int GetCount(Shorty shorty);
    }

    class AssertLogFinder : LogFinder
    {
        public AssertLogFinder(Program program, int numberOfTests, bool runTimeTest) : base(program, numberOfTests, runTimeTest) {}

        public override int GetRemovedItemsCount(Shorty shorty)
        {
            return shorty.FindRemovableAsserts().Count;
        }

        public override int GetCount(Shorty shorty)
        {
            return shorty.Asserts.Count;
        }
    }

    class InvariantLogFinder : LogFinder
    {
        public InvariantLogFinder(Program program, int numberOfTests, bool runTimeTest) : base(program, numberOfTests, runTimeTest) {}

        public override int GetRemovedItemsCount(Shorty shorty)
        {
            return shorty.FindRemovableInvariants().Count;
        }

        public override int GetCount(Shorty shorty)
        {
            return shorty.Invariants.Count;
        }
    }

    class DecreasesLogFinder : LogFinder
    {
        public DecreasesLogFinder(Program program, int numberOfTests, bool runTimeTest) : base(program, numberOfTests, runTimeTest) {}

        public override int GetRemovedItemsCount(Shorty shorty)
        {
            return shorty.FindRemovableDecreases().Count;
        }

        public override int GetCount(Shorty shorty)
        {
            return shorty.Decreases.Count + shorty.DecreasesWildCards.Sum(wildCardDecreases => wildCardDecreases.Count);
        }
    }

    class LemmaCallLogFinder : LogFinder
    {
        public LemmaCallLogFinder(Program program, int numberOfTests, bool runTimeTest) : base(program, numberOfTests, runTimeTest) {}

        public override int GetRemovedItemsCount(Shorty shorty)
        {
            return shorty.FindRemovableLemmaCalls().Count;
        }

        public override int GetCount(Shorty shorty)
        {
            return shorty.LemmaCalls.Count;
        }
    }

    class CalcLogFinder : LogFinder
    {
        public CalcLogFinder(Program program, int numberOfTests, bool runTimeTest) : base(program, numberOfTests, runTimeTest) {}

        public override int GetRemovedItemsCount(Shorty shorty)
        {
            var data = shorty.FindRemovableCalcs();
            return data.Item1.Count + data.Item2.Count;
        }

        public override int GetCount(Shorty shorty)
        {
            var calcPartCount = 0;
            foreach (var calcWrap in shorty.Calcs) {
                var calcStmt = (CalcStmt) calcWrap.Removable;
                calcPartCount += calcStmt.Hints.Count(hint => hint.Body.Count > 0);
                calcPartCount += calcStmt.Lines.Count - 1; // -1 because of the dummy
            }
            return calcPartCount;
        }
    }

    abstract class SimpLogFinder : LogFinder
    {
        public SimpLogFinder(Program program, int numberOfTests, bool runTimeTest) : base(program, numberOfTests, runTimeTest) {}

        protected abstract void RemoveAllOfType(Shorty shorty);

        protected abstract void Simplify(Shorty shorty);

        protected abstract int CountSubExprsFromItems(Shorty shorty);

        public override int GetRemovedItemsCount(Shorty shorty)
        {
            RemoveAllOfType(shorty); //we do not want theese here - this will take a bit of time but is needed for accurate results
            var initialAmount = CountSubExprsFromItems(shorty);
            Simplify(shorty);
            int after = CountSubExprsFromItems(shorty);
            var amount = initialAmount - after;
            return amount;
        }

        public int CountExpr(Expression expr)
        {
            var binExpr = expr as BinaryExpr;
            if (binExpr == null || binExpr.Op != BinaryExpr.Opcode.And) return 1;
            return CountExpr(binExpr.E0) + CountExpr(binExpr.E1);
        }

        public override int GetCount(Shorty shorty)
        {
            RemoveAllOfType(shorty);
            return CountSubExprsFromItems(shorty);
        }
    }

    class AssertSimpLogFinder : SimpLogFinder
    {
        public AssertSimpLogFinder(Program program, int numberOfTests, bool runTimeTest) : base(program, numberOfTests, runTimeTest) {}

        protected override void RemoveAllOfType(Shorty shorty)
        {
            shorty.FindRemovableAsserts();
        }

        protected override int CountSubExprsFromItems(Shorty shorty)
        {
            var amount = 0;
            foreach (var wrap in shorty.Asserts) {
                var assert = (AssertStmt) wrap.Removable;
                if (assert == null) continue;
                amount += CountExpr(assert.Expr);
            }
            return amount;
        }

        protected override void Simplify(Shorty shorty)
        {
            shorty.GetSimplifiedAsserts();
        }
    }

    class InvariantSimpLogFinder : SimpLogFinder
    {
        public InvariantSimpLogFinder(Program program, int numberOfTests, bool runTimeTest) : base(program, numberOfTests, runTimeTest) {}

        protected override void RemoveAllOfType(Shorty shorty)
        {
            shorty.FindRemovableInvariants();
        }

        protected override void Simplify(Shorty shorty)
        {
            shorty.GetSimplifiedInvariants();
        }

        protected override int CountSubExprsFromItems(Shorty shorty)
        {
            var amount = 0;
            foreach (var wrap in shorty.Invariants) {
                var invariant = wrap.Removable;
                if (invariant == null) continue;
                amount += CountExpr(invariant.E);
            }
            return amount;
        }
    }

    #endregion

    class SimpleCloner
    {
        public static Program CloneProgram(Program program)
        {
            var cloner = new Cloner();
            var moduleDecl = new LiteralModuleDecl(cloner.CloneModuleDefinition(program.DefaultModuleDef, program.Name), null);
            return new Program(program.FullName, moduleDecl, program.BuiltIns, new InvisibleErrorReporter());
        }
    }
}
