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
        private readonly int _numberOfTests = 1;

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
            _tw.WriteLine("Program Name, Asserts Before, Asserts After, Asserts Removed, Removal Percentage, Average Execution Time(ms)");

            var assertData = AssertRemoval();
            LogTupleListData(assertData);

            //Invariants
            _tw.WriteLine("\nInvariant Removal");
            _tw.WriteLine("Program Name, Invariants Before, Invariants After, Invariants Removed, Average Execution Time(ms)");

            var invariantData = InvariantRemoval();
            LogTupleListData(invariantData);

            //Lemma Call
            _tw.WriteLine("\nLemma Call Removal");
            _tw.WriteLine("Program Name, Lemma Calls Before, Lemma Calls After, Lemma Calls Removed, Average Execution Time(ms)");

            var lemmaCallData = LemmaCallRemoval();
            LogTupleListData(lemmaCallData);


            //Decreases
            _tw.WriteLine("Decreases Removal");
            _tw.WriteLine("\nProgram Name, Decreaseses Before, Decreases After, Decreaseses Removed, Average Execution Time(ms)");

            var decreasesData = DecreasesRemoval();
            LogTupleListData(decreasesData);
        }

        private void LogTupleListData(List<Tuple<string, int, int, float>> data)
        {
            var totalBefore = 0;
            var totalRemoved = 0;
            var totalAfter = 0;
            float totalTime = 0;

            foreach (var tuple in data) {
                var name = tuple.Item1;
                var before = tuple.Item2;
                var removed = tuple.Item3;
                var after = before - removed;
                var percentage = 100f - ((float) after/(float) before)*100f;
                var time = tuple.Item4;

                _tw.WriteLine("{0}, {1}, {2}, {3}, {4}, {5}", name, before, after, removed, percentage + "%", time);

                totalBefore += before;
                totalRemoved += removed;
                totalAfter += after;
                totalTime += time;
            }

            var overAllPercentage = 100f - ((float) totalAfter/(float) totalBefore)*100;
            _tw.WriteLine("Total, {0}, {1}, {2}, {3}, {4}", totalBefore, totalAfter, totalRemoved, overAllPercentage + "%", totalTime);
        }

        public List<Tuple<string, int, int, float>> AssertRemoval()
        {
            var assertData = new List<Tuple<string, int, int, float>>();

            foreach (var program in _programs) {
                Console.WriteLine("\nRemoving Asserts from {0}", program.FullName);
                var assertsBefore = 0;
                var assertsRemoved = 0;
                float averageExecutionTime = 0;
                var valid = true;
                // Run each test and add up the time of each one so the average can be found
                for (var i = 0; i < _numberOfTests; i++) {
                    var shorty = new Shorty(CloneProgram(program), Shorty.Mode.Singular);
                    if (i == 0) {
                        //Find out how many asserts were in the program before the removal - only do on first run
                        foreach (var stmt in shorty.asserts.Keys) {
                            assertsBefore += shorty.asserts[stmt].Count;
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
                }

                if (!valid)
                    continue;

                //Calculate average execution time and
                averageExecutionTime = averageExecutionTime/_numberOfTests;
                assertData.Add(new Tuple<string, int, int, float>(program.FullName, assertsBefore, assertsRemoved, averageExecutionTime));
            }
            return assertData;
        }

        public List<Tuple<string, int, int, float>> InvariantRemoval()
        {
            var invariantData = new List<Tuple<string, int, int, float>>();

            foreach (var program in _programs) {
                Console.WriteLine("\nRemoving invariants from {0}", program.FullName);
                var invariantsBefore = 0;
                var invariantsRemoved = 0;
                float averageExecutionTime = 0;
                var valid = true;

                for (var i = 0; i < _numberOfTests; i++) {
                    var shorty = new Shorty(CloneProgram(program), Shorty.Mode.Singular);
                    if (i == 0) {
                        //Find out how many invariants were in the program before the removal - only do on first run
                        foreach (var stmt in shorty.invariants.Keys) {
                            invariantsBefore += shorty.invariants[stmt].Count;
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
                }
                if (!valid)
                    continue;

                //Calculate average execution time and
                averageExecutionTime = averageExecutionTime/_numberOfTests;
                invariantData.Add(new Tuple<string, int, int, float>(program.FullName, invariantsBefore, invariantsRemoved, averageExecutionTime));
            }
            return invariantData;
        }

        public List<Tuple<string, int, int, float>> LemmaCallRemoval()
        {
            var lemmaCallData = new List<Tuple<string, int, int, float>>();
            foreach (var program in _programs) {
                Console.WriteLine("\nRemoving lemma calls from {0}", program.FullName);
                var lemmaCallsBefore = 0;
                var lemmaCallsRemoved = 0;
                float averageExecutionTime = 0;
                var valid = true;

                for (var i = 0; i < _numberOfTests; i++) {
                    var shorty = new Shorty(CloneProgram(program), Shorty.Mode.Singular);
                    if (i == 0) {
                        //Find out how many invariants were in the program before the removal - only do on first run
                        foreach (var stmt in shorty.lemmaCalls.Keys) {
                            lemmaCallsBefore += shorty.lemmaCalls[stmt].Count;
                        }
                    }

                    var sw = new Stopwatch();
                    sw.Start();
                    var lemmaCalls = shorty.FindRemovableLemmaCalls();
                    sw.Stop();

                    averageExecutionTime += sw.ElapsedMilliseconds;

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
                lemmaCallData.Add(new Tuple<string, int, int, float>(program.FullName, lemmaCallsBefore, lemmaCallsRemoved, averageExecutionTime));
            }
            return lemmaCallData;
        }

        public List<Tuple<string, int, int, float>> DecreasesRemoval()
        {
            var decreasesData = new List<Tuple<string, int, int, float>>();

            foreach (var program in _programs) {
                Console.WriteLine("\nRemoving decreases from {0}", program.FullName);
                var decreasesBefore = 0;
                var decreasesRemoved = 0;
                float averageExecutionTime = 0;
                var valid = true;

                for (var i = 0; i < _numberOfTests; i++) {
                    var shorty = new Shorty(CloneProgram(program), Shorty.Mode.Singular);
                    if (i == 0) {
                        //Find out how many invariants were in the program before the removal - only do on first run
                        foreach (var method in shorty.decreases.Keys) {
                            decreasesBefore += shorty.decreases[method].Count;
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

                    //Gather all other needed information in the first run
                    if (i == 0) {
                        decreasesRemoved = decreases.Count;
                    }
                }

                if (!valid)
                    continue;

                //Calculate average execution time and
                averageExecutionTime = averageExecutionTime/_numberOfTests;
                decreasesData.Add(new Tuple<string, int, int, float>(program.FullName, decreasesBefore, decreasesRemoved, averageExecutionTime));
            }
            return decreasesData;
        }
    }
}
