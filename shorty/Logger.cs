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
        private readonly TextWriter _tw;
        public readonly List<Program> Programs;
        public readonly List<Program> InvalidPrograms = new List<Program>();
        private readonly int _numberOfTests = 1;
        private readonly bool _runTimeTests = true;

        public Logger(TextWriter tw, List<Program> programs, int numberOfTest, bool runTimeTests = true)
        {
            Contract.Requires(numberOfTest > 0);
            if (numberOfTest > 1 && !runTimeTests) {
                throw new Exception("not running time tests and having more than one testrun - there is literally no reason to ever do this");
            }
            _numberOfTests = numberOfTest;
            _tw = tw;
            _runTimeTests = runTimeTests;
            Programs = programs;
            EnsureProgramsVerify();
        }

        public Logger(TextWriter tw, List<Program> programs)
        {
            _tw = tw;
            Programs = programs;
            EnsureProgramsVerify();
        }

        private void EnsureProgramsVerify()
        {
            for (var i = Programs.Count - 1; i >= 0; i--) {
                var program = Programs[i];
                if (EnsureProgramVerifies(program)) continue;
                InvalidPrograms.Add(program);
                Console.WriteLine("Program {0} is not valid", program.Name);
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
            if (!shorty.IsProgramValid()) return false;
            Console.WriteLine("Program {0} is valid", copy.Name);
            return true;
        }

        private Program CloneProgram(Program program)
        {
            var cloner = new Cloner();
            var moduleDecl = new LiteralModuleDecl(cloner.CloneModuleDefinition(program.DefaultModuleDef, program.Name), null);
            return new Program(program.FullName, moduleDecl, program.BuiltIns, new InvisibleErrorReproter());
        }

        private void WriteHeadings(string heading, string thing)
        {
            _tw.WriteLine("\n" + heading);
            _tw.Write("Program Name, {0} Before, {0} After, {0} Removed, Removal Percentage", thing);
            if (_runTimeTests)
                _tw.WriteLine(", Avg Execution Time(ms), Avg Verification Time Before, Avg Verification Time After, Avg Verification Time Improvement");
            else
                _tw.WriteLine();
        }

        public void LogAllData()
        {
            _tw.WriteLine("Logging data for {0} programs", Programs.Count);
            _tw.WriteLine("\nPrograms that failed initial verification");
            foreach (var program in InvalidPrograms) {
                _tw.WriteLine(program.FullName);
            }

            //Assertions
            WriteHeadings("Assert removal", "Asserts");

            var assertData = new List<Tuple<string, int, int, float, float, float>>();
            foreach (var program in Programs) {
                var logFinder = new AssertLogFinder(program, _numberOfTests, _runTimeTests);
                try {
                    Console.WriteLine("Removing asserts from {0}...", program.Name);
                    assertData.Add(logFinder.GetLogData());
                }
                catch (Exception e) {
                    _tw.WriteLine("{0}, FAILED, {1}", program.Name, e.Message);
                    Console.WriteLine("Failed to remove asserts from {0}", program.Name);
                }
            }

            LogTupleListData(assertData);

            //Assert simplification
            WriteHeadings("Assert Simplification", "Assert Subexpressions");
            var assertSimpData = new List<Tuple<string, int, int, float, float, float>>();
            foreach (var program in Programs) {
                var logFinder = new AssertSimpLogFinder(program, _numberOfTests, _runTimeTests);
                try {
                    Console.WriteLine("Simplifying asserts in {0}...", program.Name);
                    assertSimpData.Add(logFinder.GetLogData());
                }
                catch (Exception e) {
                    _tw.WriteLine("{0}, FAILED, {1}", program.Name, e.Message);
                    Console.WriteLine("Failed to simplify asserts in {0}", program.Name);
                }
            }

            LogTupleListData(assertSimpData);

            //Invariants
            WriteHeadings("Invariant removal", "Invariants");
            var invariantData = new List<Tuple<string, int, int, float, float, float>>();
            foreach (var program in Programs) {
                var logFinder = new InvariantLogFinder(program, _numberOfTests, _runTimeTests);
                try {
                    Console.WriteLine("Removing invariants from {0}...", program.Name);
                    invariantData.Add(logFinder.GetLogData());
                }
                catch (Exception e) {
                    _tw.WriteLine("{0}, FAILED, {1}", program.Name, e.Message);
                    Console.WriteLine("Failed to remove invariants from {0}", program.Name);
                }
            }
            LogTupleListData(invariantData);

            //Invariant simplification
            WriteHeadings("Invariant Simplification", "Invariant Subexpressions");
            var invariantSimpData = new List<Tuple<string, int, int, float, float, float>>();
            foreach (var program in Programs) {
                var logFinder = new InvariantSimpLogFinder(program, _numberOfTests, _runTimeTests);
                try {
                    Console.WriteLine("Simplifying invariants in {0}...", program.Name);
                    invariantSimpData.Add(logFinder.GetLogData());
                }
                catch (Exception e) {
                    _tw.WriteLine("{0}, FAILED, {1}", program.Name, e.Message);
                    Console.WriteLine("Failed to simplify invariants in {0}", program.Name);
                }
            }

            LogTupleListData(invariantSimpData);

            //Lemma Call
            WriteHeadings("Lemma Call Removal", "Lemma Calls");
            var lemmaCallData = new List<Tuple<string, int, int, float, float, float>>();
            foreach (var program in Programs) {
                var logFinder = new LemmaCallLogFinder(program, _numberOfTests, _runTimeTests);
                try {
                    Console.WriteLine("Removing lemmaCalls from {0}...", program.Name);
                    lemmaCallData.Add(logFinder.GetLogData());
                }
                catch (Exception e) {
                    _tw.WriteLine("{0}, FAILED, {1}", program.Name, e.Message);
                    Console.WriteLine("Failed to remove lemma calls from {0}", program.Name);
                }
            }
            LogTupleListData(lemmaCallData);


            //Decreases
            WriteHeadings("Decreases Removal", "Decreases");
            var decreasesData = new List<Tuple<string, int, int, float, float, float>>();
            foreach (var program in Programs) {
                var logFinder = new DecreasesLogFinder(program, _numberOfTests, _runTimeTests);
                try {
                    Console.WriteLine("Removing decreases from {0}...", program.Name);
                    decreasesData.Add(logFinder.GetLogData());
                }
                catch (Exception e) {
                    _tw.WriteLine("{0}, FAILED, {1}", program.Name, e.Message);
                    Console.WriteLine("Failed to remove decreases from {0}", program.Name);
                }
            }
            LogTupleListData(decreasesData);


            //Calc
            WriteHeadings("Calc Simplification", "Calc Parts");
            var calcData = new List<Tuple<string, int, int, float, float, float>>();
            foreach (var program in Programs) {
                var logFinder = new CalcLogFinder(program, _numberOfTests, _runTimeTests);
                try {
                    Console.WriteLine("Removing calcs from {0}...", program.Name);
                    calcData.Add(logFinder.GetLogData());
                }
                catch (Exception e) {
                    _tw.WriteLine("{0}, FAILED, {1}", program.Name, e.Message);
                    Console.WriteLine("Failed to remove calcs from {0}", program.Name);
                }
            }
            LogTupleListData(calcData);
        }

        private void LogTupleListData(List<Tuple<string, int, int, float, float, float>> data)
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
                    _tw.WriteLine("{0}, {1}, {2}, {3}, {4}, {5}, {6}, {7}, {8}", name, before, after, removed, percentage + "%", executionTime, verTimeBefore, verTimeAfter, verTimeImprovement);
                    totalTime += executionTime;
                    totalVerTimeBefore += verTimeBefore;
                    totalVerTimeAfter += verTimeAfter;
                }
                else
                    _tw.WriteLine("{0}, {1}, {2}, {3}, {4}", name, before, after, removed, percentage + "%");
            }

            var overAllPercentage = 100f - ((float) totalAfter/(float) totalBefore)*100;
            if (_runTimeTests) {
                var totalVerTimeImprovement = totalVerTimeBefore - totalVerTimeAfter;
                _tw.WriteLine("Total, {0}, {1}, {2}, {3}, {4}, {5}, {6}, {7}", totalBefore, totalAfter, totalRemoved, overAllPercentage + "%", totalTime, totalVerTimeBefore, totalVerTimeAfter, totalVerTimeImprovement);
                _tw.WriteLine(",,,,,,,Avg ver Time Improvement:,{0}", totalVerTimeImprovement/Programs.Count);
            }
            else
                _tw.WriteLine("Total, {0}, {1}, {2}, {3}", totalBefore, totalAfter, totalRemoved, overAllPercentage + "%");
        }
    }

    #region LogFinders

    abstract class LogFinder
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
            var amount = initialAmount - CountSubExprsFromItems(shorty);
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
            return new Program(program.FullName, moduleDecl, program.BuiltIns, new InvisibleErrorReproter());
        }
    }
}
