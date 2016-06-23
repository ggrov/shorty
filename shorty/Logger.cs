using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Diagnostics.Contracts;
using Microsoft.Dafny;

namespace shorty
{
    class Logger
    {
        private readonly TextWriter _tw;
        private readonly List<Program> _programs;
        private readonly int _numberOfTests = 2;

        public Logger(TextWriter tw, List<Program> programs, int numberOfTest)
        {
            Contract.Requires(numberOfTest > 0);
            _numberOfTests = numberOfTest;
            _tw = tw;
            _programs = programs;
        }

        public Logger(TextWriter tw, List<Program> programs)
        {
            _tw = tw;
            _programs = programs;
        }

        private Program CloneProgram(Program program)
        {
            var cloner = new Cloner();
            var moduleDecl = new LiteralModuleDecl(cloner.CloneModuleDefinition(program.DefaultModuleDef, program.Name), null);
            return new Program(program.FullName, moduleDecl, program.BuiltIns);
        }

        public void LogAllData()
        {
            _tw.WriteLine("Logging data for {0} programs", _programs.Count);
            _tw.WriteLine("");

            //Assertions
            _tw.WriteLine("Assert Removal");
            _tw.WriteLine("Program Name, Asserts Before, Asserts After, Asserts Removed, Removal Percentage, Avg Execution Time(ms), Avg Verification Time Before, Avg Verification Time After, Verification Time Improvement");

            var assertData = AssertRemoval();
            LogTupleListData(assertData);

            //Invariants
            _tw.WriteLine("\nInvariant Removal");
            _tw.WriteLine("Program Name, Invariants Before, Invariants After, Invariants Removed, Removal Percentage, Avg Execution Time(ms), Avg Verification Time Before, Avg Verification Time After, Average Verification Time Improvement");

            var invariantData = InvariantRemoval();
            LogTupleListData(invariantData);

            //Lemma Call
            _tw.WriteLine("\nLemma Call Removal");
            _tw.WriteLine("Program Name, Lemma Calls Before, Lemma Calls After, Lemma Calls Removed, Removal Percentage, Avg Execution Time(ms), Avg Verification Time Before, Avg Verification Time After, Average Verification Time Improvement");

            var lemmaCallData = LemmaCallRemoval();
            LogTupleListData(lemmaCallData);


            //Decreases
            _tw.WriteLine("Decreases Removal");
            _tw.WriteLine("\nProgram Name, Decreaseses Before, Decreases After, Decreaseses Removed, Removal Percentage, Avg Execution Time(ms), Avg Verification Time Before, Avg Verification Time After, Average Verification Time Improvement");

            var decreasesData = DecreasesRemoval();
            LogTupleListData(decreasesData);
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
            _tw.WriteLine("Total, {0}, {1}, {2}, {3}, {4}, {5}, {6}, {7}", totalBefore, totalAfter, totalRemoved, overAllPercentage + "%",
                totalTime, totalVerTimeBefore, totalVerTimeAfter, totalVerTimeImprovement);
            _tw.WriteLine(",,,,,,,Avg ver Time Improvement:,{0}", totalVerTimeImprovement/_programs.Count);
        }

        public long FindExecutionTime(Program program)
        {
            Shorty shorty = new Shorty(CloneProgram(program));
            Stopwatch watch = new Stopwatch();
            watch.Start();
            if (!shorty.IsProgramValid())
                return -1;
            watch.Stop();
            return watch.ElapsedMilliseconds;
        }

        public List<Tuple<string, int, int, float, float, float>> AssertRemoval()
        {
            var assertData = new List<Tuple<string, int, int, float, float, float>>();

            foreach (var program in _programs) {
                Console.WriteLine("\nRemoving Asserts from {0}", program.FullName);
                var assertsBefore = 0;
                var assertsRemoved = 0;
                float averageExecutionTime = 0;
                var valid = true;
                float averageTimeBefore = 0;
                float averageTimeAfter = 0;

                // Run each test and add up the time of each one so the average can be found
                for (var i = 0; i < _numberOfTests; i++) {
                    var programClone = CloneProgram(program);
                    var shorty = new Shorty(programClone);

                    averageTimeBefore += FindExecutionTime(programClone);
                    
                    if (i == 0) {
                        //Find out how many asserts were in the program before the removal - only do on first run
                        foreach (var method in shorty.Asserts.Keys) {
                            foreach (var stmt in shorty.Asserts[method].Keys) {
                                assertsBefore += shorty.Asserts[method][stmt].Count;                                
                            }
                        }
                    }

                    var sw = new Stopwatch();
                    sw.Start();
                    var asserts = shorty.FindUnnecessaryAsserts();
                    sw.Stop();

                    if (asserts == null) {
                        _tw.WriteLine(program.Name + "Failed to find asserts");
                        valid = false;
                        break;
                    }

                    averageExecutionTime += sw.ElapsedMilliseconds;

                    //Gather all other needed information in the first run
                    if (i == 0) {
                        assertsRemoved = asserts.Count;
                    }

                    averageTimeAfter += FindExecutionTime(programClone);
                }

                if (!valid)
                    continue;
                
                //Calculate average execution time and
                averageExecutionTime = averageExecutionTime/_numberOfTests;
                averageTimeBefore = averageTimeBefore/_numberOfTests;
                averageTimeAfter = averageTimeAfter/_numberOfTests;
                assertData.Add(new Tuple<string, int, int, float, float,float>(program.FullName, assertsBefore, assertsRemoved,
                    averageExecutionTime, averageTimeBefore, averageTimeAfter));
            }
            return assertData;
        }

        public List<Tuple<string, int, int, float, float, float>> InvariantRemoval()
        {
            var invariantData = new List<Tuple<string, int, int, float, float, float>>();

            foreach (var program in _programs) {
                Console.WriteLine("\nRemoving invariants from {0}", program.FullName);
                var invariantsBefore = 0;
                var invariantsRemoved = 0;
                float averageExecutionTime = 0;
                var valid = true;
                float averageTimeBefore = 0;
                float averageTimeAfter = 0;

                for (var i = 0; i < _numberOfTests; i++) {
                    var programClone = CloneProgram(program);
                    var shorty = new Shorty(programClone);

                    //Find the verificaiton time before the shorty method is run
                    averageTimeBefore += FindExecutionTime(programClone);

                    if (i == 0) {
                        //Find out how many invariants were in the program before the removal - only do on first run
                        foreach (var stmt in shorty.Invariants.Keys) {
                            invariantsBefore += shorty.Invariants[stmt].Count;
                        }
                    }

                    var sw = new Stopwatch();
                    sw.Start();
                    var invariants = shorty.FindRemovableInvariants();
                    sw.Stop();

                    if (invariants == null) {
                        _tw.WriteLine(program.Name + "Failed to find invariants");
                        valid = false;
                        break;
                    }

                    averageExecutionTime += sw.ElapsedMilliseconds;

                    //Gather all other needed information in the first run
                    if (i == 0) {
                        invariantsRemoved = invariants.Count;
                    }

                    averageTimeAfter += FindExecutionTime(programClone);
                }
                if (!valid)
                    continue;

                //Calculate average execution time and
                averageExecutionTime = averageExecutionTime/_numberOfTests;
                averageTimeBefore = averageTimeBefore / _numberOfTests;
                averageTimeAfter = averageTimeAfter / _numberOfTests;
                invariantData.Add(new Tuple<string, int, int, float, float, float>(program.FullName, invariantsBefore, invariantsRemoved, 
                    averageExecutionTime, averageTimeBefore, averageTimeAfter));
            }
            return invariantData;
        }

        public List<Tuple<string, int, int, float, float, float>> LemmaCallRemoval()
        {
            var lemmaCallData = new List<Tuple<string, int, int, float, float, float>>();
            foreach (var program in _programs) {
                Console.WriteLine("\nRemoving lemma calls from {0}", program.FullName);
                var lemmaCallsBefore = 0;
                var lemmaCallsRemoved = 0;
                float averageExecutionTime = 0;
                var valid = true;
                float averageTimeBefore = 0;
                float averageTimeAfter = 0;

                for (var i = 0; i < _numberOfTests; i++) {
                    var programClone = CloneProgram(program);
                    var shorty = new Shorty(programClone);

                    //Find the verificaiton time before the shorty method is run
                    averageTimeBefore += FindExecutionTime(programClone);

                    if (i == 0)
                    {
                        //Find out how many invariants were in the program before the removal - only do on first run
                        foreach (var stmt in shorty.LemmaCalls.Keys) {
                            lemmaCallsBefore += shorty.LemmaCalls[stmt].Count;
                        }
                    }

                    var sw = new Stopwatch();
                    sw.Start();
                    var lemmaCalls = shorty.FindRemovableLemmaCalls();
                    sw.Stop();

                    averageExecutionTime += sw.ElapsedMilliseconds;
                    averageTimeAfter += FindExecutionTime(programClone);

                    if (lemmaCalls == null) {
                        _tw.WriteLine(program.Name + "Failed to find Lemma calls");
                        valid = false;
                        break;
                    }

                    //Gather all other needed information in the first run
                    if (i == 0) {
                        lemmaCallsRemoved = lemmaCalls.Count;
                    }
                }

                if (!valid)
                    continue;

                //Calculate average execution time and
                averageExecutionTime = averageExecutionTime/_numberOfTests;
                averageTimeBefore = averageTimeBefore / _numberOfTests;
                averageTimeAfter = averageTimeAfter / _numberOfTests;
                lemmaCallData.Add(new Tuple<string, int, int, float, float, float>(program.FullName, lemmaCallsBefore, lemmaCallsRemoved, 
                    averageExecutionTime, averageTimeBefore, averageTimeAfter));
            }
            return lemmaCallData;
        }

        public List<Tuple<string, int, int, float, float, float>> DecreasesRemoval()
        {
            var decreasesData = new List<Tuple<string, int, int, float, float, float>>();

            foreach (var program in _programs) {
                Console.WriteLine("\nRemoving decreases from {0}", program.FullName);
                var decreasesBefore = 0;
                var decreasesRemoved = 0;
                float averageExecutionTime = 0;
                var valid = true;
                float averageTimeBefore = 0;
                float averageTimeAfter = 0;

                for (var i = 0; i < _numberOfTests; i++) {
                    var programClone = CloneProgram(program);
                    var shorty = new Shorty(programClone);

                    //Find the verificaiton time before the shorty method is run
                    averageTimeBefore += FindExecutionTime(programClone);
                    
                    if (i == 0)
                    {
                        //Find out how many invariants were in the program before the removal - only do on first run
                        foreach (var method in shorty.Decreases.Keys) {
                            decreasesBefore += shorty.Decreases[method].Count;
                        }
                    }

                    var sw = new Stopwatch();
                    sw.Start();
                    var decreases = shorty.FindRemoveableDecreases();
                    sw.Stop();
                    if (decreases == null) {
                        _tw.WriteLine(program.Name + "Failed to find decreases");
                        valid = false;
                        break;
                    }

                    averageExecutionTime += sw.ElapsedMilliseconds;
                    averageTimeAfter += FindExecutionTime(programClone);

                    //Gather all other needed information in the first run
                    if (i == 0) {
                        decreasesRemoved = decreases.Count;
                    }
                }

                if (!valid)
                    continue;

                //Calculate average execution time and
                averageExecutionTime = averageExecutionTime/_numberOfTests;
                averageTimeBefore = averageTimeBefore / _numberOfTests;
                averageTimeAfter = averageTimeAfter / _numberOfTests;
                decreasesData.Add(new Tuple<string, int, int, float, float, float>(program.FullName, decreasesBefore, decreasesRemoved, 
                    averageExecutionTime, averageTimeBefore, averageTimeAfter));
            }
            return decreasesData;
        }
    }
}
