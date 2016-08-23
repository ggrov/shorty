using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;
using Microsoft.Dafny;
using Bpl = Microsoft.Boogie;
using Program = Microsoft.Dafny.Program;
using Dary;

namespace DaryTools
{
    internal class Logger
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
            var daryController = new DaryController(copy);
            return daryController.IsProgramValid();
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

            LogFile("assert-removal", "Asserts", new AssertLogFinderFactory());
            LogFile("assert-simplification","Assert Subexpressions", new AssertSimpLogFinderFactory());
            LogFile("invariant-removal", "Invariants", new InvariantLogFinderFactory());
            LogFile("invariant-simplification","Invariant Subexpressions", new InvariantSimpLogFinderFactory());
            LogFile("lemma-call-removal", "Lemma Calls", new LemmaCallLogFinderFactory());
            LogFile("decreases-removal", "Decreases", new DecreasesLogFinderFactory());
            LogFile("calc-removal", "Calc Parts", new CalcLogFinderFactory());
            if(_runTimeTests)
                LogFile("everything-removal", "", new EverythingLogFinderFactory()); //This will not actually count anything as the information will not be entirely useful (e.g. does a part of an assert count as much as an assert?)
        }

        private void LogFile(string fileName, string itemsName, ILogFinderFactory logFinderFactory)
        {
            var fullFileName = _directory + fileName + ".csv";
            using (TextWriter tw = File.CreateText(fullFileName))
            {
                WriteHeadings(tw, itemsName);
                var count = 1;
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

                var numberOfPrograms = 0;

                foreach (var tuple in data) {
                    var before = tuple.Item2;
                    if (before == 0) continue;
                    numberOfPrograms++;
                }
                tw.WriteLine("{0}/{1} programs found contain {2}", numberOfPrograms, data.Count, itemsName);
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

            

            tw.WriteLine("{0} programs containing");

            foreach (var tuple in data) {
                var name = tuple.Item1;
                var before = tuple.Item2;
                if(before == 0) continue;
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
                tw.WriteLine("{0}, {1}, {2}, {3}, {4}, {5}, {6}, {7}", totalBefore, totalAfter, totalRemoved, overAllPercentage + "%", totalTime, totalVerTimeBefore, totalVerTimeAfter, totalVerTimeImprovement);
                tw.WriteLine(",,,,,,,Avg ver Time Improvement:,{0}", totalVerTimeImprovement/Programs.Count);
            }
            else
                tw.WriteLine("Total, {0}, {1}, {2}, {3}", totalBefore, totalAfter, totalRemoved, overAllPercentage + "%");
        }
    }

    #region LogFinder Factories

    internal interface ILogFinderFactory
    {
        LogFinder GetLogFinder(Program program, int numberOfTests, bool runTimeTests);
    }

    internal class AssertLogFinderFactory : ILogFinderFactory
    {
        public LogFinder GetLogFinder(Program program, int numberOfTests, bool runTimeTests)
        {
            return new AssertLogFinder(program, numberOfTests, runTimeTests);
        }
    }

    internal class AssertSimpLogFinderFactory : ILogFinderFactory
    {
        public LogFinder GetLogFinder(Program program, int numberOfTests, bool runTimeTests)
        {
            return new AssertSimpLogFinder(program, numberOfTests, runTimeTests);
        }
    }

    internal class InvariantLogFinderFactory : ILogFinderFactory
    {
        public LogFinder GetLogFinder(Program program, int numberOfTests, bool runTimeTests)
        {
            return new InvariantLogFinder(program, numberOfTests, runTimeTests);
        }
    }

    internal class InvariantSimpLogFinderFactory : ILogFinderFactory
    {
        public LogFinder GetLogFinder(Program program, int numberOfTests, bool runTimeTests)
        {
            return new InvariantSimpLogFinder(program, numberOfTests, runTimeTests);
        }
    }

    internal class LemmaCallLogFinderFactory : ILogFinderFactory
    {
        public LogFinder GetLogFinder(Program program, int numberOfTests, bool runTimeTests)
        {
            return new LemmaCallLogFinder(program, numberOfTests, runTimeTests);
        }
    }

    internal class DecreasesLogFinderFactory : ILogFinderFactory
    {
        public LogFinder GetLogFinder(Program program, int numberOfTests, bool runTimeTests)
        {
            return new DecreasesLogFinder(program, numberOfTests, runTimeTests);
        }
    }

    internal class CalcLogFinderFactory : ILogFinderFactory
    {
        public LogFinder GetLogFinder(Program program, int numberOfTests, bool runTimeTests)
        {
            return new CalcLogFinder(program, numberOfTests, runTimeTests);
        }
    }
    internal class EverythingLogFinderFactory : ILogFinderFactory
    {
        public LogFinder GetLogFinder(Program program, int numberOfTests, bool runTimeTests)
        {
            return new EverythingLogFinder(program, numberOfTests, runTimeTests);
        }
    }


    #endregion

    #region LogFinders

    internal abstract class LogFinder
    {
        protected Program Program;
        private readonly int _numberOfTests;
        private readonly bool _runTimeTests;

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
                var daryController = new DaryController(programClone);
                var runData = RunTest(daryController);
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
            var daryController = new DaryController(programClone);
            var countBefore = GetCount(daryController);
            var data = new Tuple<long, long, long>(0, 0, 0);
            if (_runTimeTests)
                data = RunTest(daryController);
            else
                GetRemovedItemsCount(daryController);
            var countAfter = GetCount(daryController);
            if (!daryController.IsProgramValid()) {
//                using (TextWriter writer = File.CreateText("H:\\dafny\\programs\\shotied\\short-"+daryController.Program.Name)) {
//                    daryController.PrintProgram(writer);
//                }
                throw new Exception("Program not valid after initial test!");

            }
            return new Tuple<long, long, long, int, int>(data.Item1, data.Item2, data.Item3, countBefore, countAfter);
        }

        /// <summary>
        /// </summary>
        /// <returns>A tuple containing the execution time, the verification time before and the verification time after</returns>
        private Tuple<long, long, long> RunTest(DaryController daryController)
        {
            var daryExecutionTimeStopwatch = new Stopwatch();
            var verificationTimeBefore = GetVerificationTime(daryController);
            daryExecutionTimeStopwatch.Start();
            GetRemovedItemsCount(daryController);
            daryExecutionTimeStopwatch.Stop();
            var verificationTimeAfter = GetVerificationTime(daryController);
            return new Tuple<long, long, long>(daryExecutionTimeStopwatch.ElapsedMilliseconds, verificationTimeBefore, verificationTimeAfter);
        }

        private long GetVerificationTime(DaryController daryController)
        {
            Bpl.CommandLineOptions.Clo.VerifySnapshots = 0;
            var watch = new Stopwatch();
            watch.Start();
            if (!daryController.IsProgramValid()) {
//                using (TextWriter writer = File.CreateText("H:\\dafny\\programs\\Shortied\\short-" + daryController.Program.Name)) {
//                    daryController.PrintProgram(writer);
//                }
                throw new Exception("Cannot find verification time as program is not valid!");
            }
            watch.Stop();
            Bpl.CommandLineOptions.Clo.VerifySnapshots = 1;
            return watch.ElapsedMilliseconds;
        }

        public abstract int GetRemovedItemsCount(DaryController daryController);

        public abstract int GetCount(DaryController daryController);
    }

    internal class AssertLogFinder : LogFinder
    {
        public AssertLogFinder(Program program, int numberOfTests, bool runTimeTest) : base(program, numberOfTests, runTimeTest) {}

        public override int GetRemovedItemsCount(DaryController daryController)
        {
            return daryController.FindRemovableAsserts().Count;
        }

        public override int GetCount(DaryController daryController)
        {
            return daryController.Asserts.Count;
        }
    }

    internal class InvariantLogFinder : LogFinder
    {
        public InvariantLogFinder(Program program, int numberOfTests, bool runTimeTest) : base(program, numberOfTests, runTimeTest) {}

        public override int GetRemovedItemsCount(DaryController daryController)
        {
            return daryController.FindRemovableInvariants().Count;
        }

        public override int GetCount(DaryController daryController)
        {
            return daryController.Invariants.Count;
        }
    }

    internal class DecreasesLogFinder : LogFinder
    {
        public DecreasesLogFinder(Program program, int numberOfTests, bool runTimeTest) : base(program, numberOfTests, runTimeTest) {}

        public override int GetRemovedItemsCount(DaryController daryController)
        {
            return daryController.FindRemovableDecreases().Count;
        }

        public override int GetCount(DaryController daryController)
        {
            return daryController.Decreases.Count + daryController.DecreasesWildCards.Sum(wildCardDecreases => wildCardDecreases.Count);
        }
    }

    internal class LemmaCallLogFinder : LogFinder
    {
        public LemmaCallLogFinder(Program program, int numberOfTests, bool runTimeTest) : base(program, numberOfTests, runTimeTest) {}

        public override int GetRemovedItemsCount(DaryController daryController)
        {
            return daryController.FindRemovableLemmaCalls().Count;
        }

        public override int GetCount(DaryController daryController)
        {
            return daryController.LemmaCalls.Count;
        }
    }

    internal class CalcLogFinder : LogFinder
    {
        public CalcLogFinder(Program program, int numberOfTests, bool runTimeTest) : base(program, numberOfTests, runTimeTest) {}

        public override int GetRemovedItemsCount(DaryController daryController)
        {
            var data = daryController.FindRemovableCalcs();
            return data.Item1.Count + data.Item2.Count;
        }

        public override int GetCount(DaryController daryController)
        {
            var calcPartCount = 0;
            foreach (var calcWrap in daryController.Calcs) {
                var calcStmt = (CalcStmt) calcWrap.Removable;
                calcPartCount += calcStmt.Hints.Count(hint => hint.Body.Count > 0);
                calcPartCount += calcStmt.Lines.Count - 1; // -1 because of the dummy
            }
            return calcPartCount;
        }
    }

    internal abstract class SimpLogFinder : LogFinder
    {
        public SimpLogFinder(Program program, int numberOfTests, bool runTimeTest) : base(program, numberOfTests, runTimeTest) {}

        protected abstract void RemoveAllOfType(DaryController daryController);

        protected abstract void Simplify(DaryController daryController);

        protected abstract int CountSubExprsFromItems(DaryController daryController);

        public override int GetRemovedItemsCount(DaryController daryController)
        {
            RemoveAllOfType(daryController); //we do not want theese here - this will take a bit of time but is needed for accurate results
            var initialAmount = CountSubExprsFromItems(daryController);
            Simplify(daryController);
            var after = CountSubExprsFromItems(daryController);
            var amount = initialAmount - after;
            return amount;
        }

        public int CountExpr(Expression expr)
        {
            var binExpr = expr as BinaryExpr;
            if (binExpr == null || binExpr.Op != BinaryExpr.Opcode.And) return 1;
            return CountExpr(binExpr.E0) + CountExpr(binExpr.E1);
        }

        public override int GetCount(DaryController daryController)
        {
            RemoveAllOfType(daryController);
            return CountSubExprsFromItems(daryController);
        }
    }

    internal class AssertSimpLogFinder : SimpLogFinder
    {
        public AssertSimpLogFinder(Program program, int numberOfTests, bool runTimeTest) : base(program, numberOfTests, runTimeTest) {}

        protected override void RemoveAllOfType(DaryController daryController)
        {
            daryController.FindRemovableAsserts();
        }

        protected override int CountSubExprsFromItems(DaryController daryController)
        {
            var amount = 0;
            foreach (var wrap in daryController.Asserts) {
                var assert = (AssertStmt) wrap.Removable;
                if (assert == null) continue;
                amount += CountExpr(assert.Expr);
            }
            return amount;
        }

        protected override void Simplify(DaryController daryController)
        {
            daryController.GetSimplifiedAsserts();
        }
    }

    internal class InvariantSimpLogFinder : SimpLogFinder
    {
        public InvariantSimpLogFinder(Program program, int numberOfTests, bool runTimeTest) : base(program, numberOfTests, runTimeTest) {}

        protected override void RemoveAllOfType(DaryController daryController)
        {
            daryController.FindRemovableInvariants();
        }

        protected override void Simplify(DaryController daryController)
        {
            daryController.GetSimplifiedInvariants();
        }

        protected override int CountSubExprsFromItems(DaryController daryController)
        {
            var amount = 0;
            foreach (var wrap in daryController.Invariants) {
                var invariant = wrap.Removable;
                if (invariant == null) continue;
                amount += CountExpr(invariant.E);
            }
            return amount;
        }
    }

    internal class EverythingLogFinder : LogFinder
    {
        public EverythingLogFinder(Program program, int numberOfTests, bool runTimeTest) : base(program, numberOfTests, runTimeTest) {}

        public override int GetRemovedItemsCount(DaryController daryController)
        {
            var amount = 0;
            amount += daryController.FindRemovableAsserts().Count;
            amount += daryController.FindRemovableInvariants().Count;
            amount += daryController.FindRemovableDecreases().Count;
            amount += daryController.FindRemovableLemmaCalls().Count;
            amount += daryController.FindRemovableCalcs().Item1.Count;
            amount += daryController.GetSimplifiedAsserts().Count;
            amount += daryController.GetSimplifiedInvariants().Count;
//            return amount;
            return 0;

        }

        public override int GetCount(DaryController daryController)
        {
            return 0;
        }
    }

    #endregion

    internal class SimpleCloner
    {
        public static Program CloneProgram(Program program)
        {
            var cloner = new Cloner();
            var moduleDecl = new LiteralModuleDecl(cloner.CloneModuleDefinition(program.DefaultModuleDef, program.Name), null);
            return new Program(program.FullName, moduleDecl, program.BuiltIns, new InvisibleErrorReporter());
        }
    }
}
