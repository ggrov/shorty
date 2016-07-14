using System;
using System.Collections.Generic;
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

        public Logger(TextWriter tw, List<Program> programs, int numberOfTest)
        {
            Contract.Requires(numberOfTest > 0);
            _numberOfTests = numberOfTest;
            _tw = tw;
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
            for (int i = Programs.Count - 1; i >= 0; i--) {
                try {
                    Console.WriteLine("Checking " + Programs[i].FullName);
                    Program copy = CloneProgram(Programs[i]);
                    Shorty shorty = new Shorty(copy);
                    if (!shorty.IsProgramValid()) {
                        InvalidPrograms.Add(Programs[i]);
                        Programs.Remove(Programs[i]);
                        Console.WriteLine("Program {0} is not valid", copy.Name);
                    }
                    else {
                        Console.WriteLine("Program {0} is valid", copy.Name);
                    }
                }
                catch {
                    InvalidPrograms.Add(Programs[i]);
                    Console.WriteLine("Program {0} is not valid!", Programs[i].Name);
                    Programs.Remove(Programs[i]);
                }
            }
        }

        private Program CloneProgram(Program program)
        {
            var cloner = new Cloner();
            var moduleDecl = new LiteralModuleDecl(cloner.CloneModuleDefinition(program.DefaultModuleDef, program.Name), null);
            return new Program(program.FullName, moduleDecl, program.BuiltIns, new InvisibleErrorReproter());
        }

        public void LogAllData()
        {
            _tw.WriteLine("Logging data for {0} programs", Programs.Count);
            _tw.WriteLine("\nPrograms that failed initial verification");
            foreach (var program in InvalidPrograms) {
                _tw.WriteLine(program.FullName);
            }

            //Assertions
            _tw.WriteLine("\nAssert Removal");
            _tw.WriteLine("Program Name, Asserts Before, Asserts After, Asserts Removed, Removal Percentage, Avg Execution Time(ms), Avg Verification Time Before, Avg Verification Time After, Avg Verification Time Improvement");


            var assertData = new List<Tuple<string, int, int, float, float, float>>();
            foreach (var program in Programs) {
                var logFinder = new AssertLogFinder(program, _numberOfTests);
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

            //Invariants
            _tw.WriteLine("\nInvariant Removal");
            _tw.WriteLine("Program Name, Invariants Before, Invariants After, Invariants Removed, Removal Percentage, Avg Execution Time(ms), Avg Verification Time Before, Avg Verification Time After, Avg Verification Time Improvement");

            var invariantData = new List<Tuple<string, int, int, float, float, float>>();
            foreach (var program in Programs) {
                var logFinder = new InvariantLogFinder(program, _numberOfTests);
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

            //Lemma Call
            _tw.WriteLine("\nLemma Call Removal");
            _tw.WriteLine("Program Name, Lemma Calls Before, Lemma Calls After, Lemma Calls Removed, Removal Percentage, Avg Execution Time(ms), Avg Verification Time Before, Avg Verification Time After, Avg Verification Time Improvement");

            var lemmaCallData = new List<Tuple<string, int, int, float, float, float>>();
            foreach (var program in Programs) {
                var logFinder = new LemmaCallLogFinder(program, _numberOfTests);
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
            _tw.WriteLine("Decreases Removal");
            _tw.WriteLine("\nProgram Name, Decreaseses Before, Decreases After, Decreaseses Removed, Removal Percentage, Avg Execution Time(ms), Avg Verification Time Before, Avg Verification Time After, Avg Verification Time Improvement");

            var decreasesData = new List<Tuple<string, int, int, float, float, float>>();
            foreach (var program in Programs) {
                var logFinder = new DecreasesLogFinder(program, _numberOfTests);
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
            _tw.WriteLine("Calc Simplification");
            _tw.WriteLine("\nProgram Name, Calc Parts Before, Calc Parts After, Calc Parts Removed, Removal Percentage, Avg Execution Time(ms), Avg Verification Time Before, Avg Verification Time After, Avg Verification Time Improvement");

            var calcData = new List<Tuple<string, int, int, float, float, float>>();
            foreach (var program in Programs) {
                var logFinder = new CalcLogFinder(program, _numberOfTests);
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
                var removed = tuple.Item3;
                var after = before - removed;
                var percentage = 100f - ((float) after/(float) before)*100f;
                var executionTime = tuple.Item4;
                var verTimeBefore = tuple.Item5;
                var verTimeAfter = tuple.Item6;
                var verTimeImprovement = verTimeBefore - verTimeAfter;

                _tw.WriteLine("{0}, {1}, {2}, {3}, {4}, {5}, {6}, {7}, {8}", name, before, after, removed, percentage + "%", executionTime, verTimeBefore, verTimeAfter, verTimeImprovement);

                totalBefore += before;
                totalRemoved += removed;
                totalAfter += after;
                totalTime += executionTime;
                totalVerTimeBefore += verTimeBefore;
                totalVerTimeAfter += verTimeAfter;
            }

            var overAllPercentage = 100f - ((float) totalAfter/(float) totalBefore)*100;
            var totalVerTimeImprovement = totalVerTimeBefore - totalVerTimeAfter;
            _tw.WriteLine("Total, {0}, {1}, {2}, {3}, {4}, {5}, {6}, {7}", totalBefore, totalAfter, totalRemoved, overAllPercentage + "%", totalTime, totalVerTimeBefore, totalVerTimeAfter, totalVerTimeImprovement);
            _tw.WriteLine(",,,,,,,Avg ver Time Improvement:,{0}", totalVerTimeImprovement/Programs.Count);
        }
    }

    #region LogFinders

    abstract class LogFinder
    {
        protected Program Program;
        private readonly int _numberOfTests;

        protected LogFinder(Program program, int numberOfTests)
        {
            Program = program;
            _numberOfTests = numberOfTests;
        }

        public Tuple<string, int, int, float, float, float> GetLogData()
        {
            float averageExecutionTime = 0;
            float averageTimeBefore = 0;
            float averageTimeAfter = 0;

            var initResults = RunInitialTest();
            var countBefore = initResults.Item4;
            var countAfter = initResults.Item5;
            averageExecutionTime += initResults.Item1;
            averageTimeBefore += initResults.Item2;
            averageTimeAfter += initResults.Item3;

            for (var i = 0; i < _numberOfTests - 1; i++) {
                Program programClone = SimpleCloner.CloneProgram(Program);
                Shorty shorty = new Shorty(programClone);
                var runData = RunTest(shorty);
                averageExecutionTime += runData.Item1;
                averageTimeBefore += runData.Item2;
                averageTimeAfter += runData.Item3;
            }
            averageExecutionTime /= _numberOfTests;
            averageTimeBefore /= _numberOfTests;
            averageTimeAfter /= _numberOfTests;

            return new Tuple<string, int, int, float, float, float>(Program.Name, countBefore, countAfter, averageExecutionTime, averageTimeBefore, averageTimeAfter);
        }

        private Tuple<long, long, long, int, int> RunInitialTest()
        {
            Program programClone = SimpleCloner.CloneProgram(Program);
            Shorty shorty = new Shorty(programClone);
            var countBefore = GetCount(shorty);
            var data = RunTest(shorty);
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
            Stopwatch watch = new Stopwatch();
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
        public AssertLogFinder(Program program, int numberOfTests) : base(program, numberOfTests) {}

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
        public InvariantLogFinder(Program program, int numberOfTests) : base(program, numberOfTests) {}

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
        public DecreasesLogFinder(Program program, int numberOfTests) : base(program, numberOfTests) {}

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
        public LemmaCallLogFinder(Program program, int numberOfTests) : base(program, numberOfTests) {}

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
        public CalcLogFinder(Program program, int numberOfTests) : base(program, numberOfTests) {}

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
