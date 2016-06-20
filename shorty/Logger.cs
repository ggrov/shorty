using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.Diagnostics.Contracts;
using Microsoft.Dafny;

namespace shorty
{
    class Logger
    {
        TextWriter tw;
        private List<Microsoft.Dafny.Program> programs;
        private List<Tuple<string, int, int, float>> assertData = new List<Tuple<string, int, int, float>>();
        private List<Tuple<string, int, int, float>> invariantData = new List<Tuple<string, int, int, float>>();
        private int testNumbers = 1;

        public Logger(TextWriter tw, List<Microsoft.Dafny.Program> programs)
        {
            this.tw = tw;
            this.programs = programs;
        }

        public void RunTests()
        {
            tw.WriteLine("Logging data for {0} programs", programs.Count);
            //Run all the tests
            TestAssertRemoval();
            tw.WriteLine("\n");
            TestInvariantRemoval();
            tw.WriteLine("\n");

            //Log out extra statistics

            //assertions
            int totalAssertions = 0;
            int totalRemovedAssertions = 0;
            foreach (var data in assertData) {
                totalAssertions += data.Item2;
                totalRemovedAssertions += data.Item3;
            }
            float percentageRemoved = (totalRemovedAssertions / totalAssertions) * 100;
            tw.WriteLine("Percentage of assertions removed: {0}", percentageRemoved);
        }

        public void TestAssertRemoval()
        {
            tw.WriteLine("Assert Removal");
            tw.WriteLine("Program Name, Asserts Before, Asserts Removed, Average Execution Time(ms)");
            
            foreach (Microsoft.Dafny.Program program in programs) {
                Console.WriteLine("\nRemoving Asserts from {0}", program.FullName);
                int assertsBefore = 0;
                int assertsRemoved = 0;
                float averageExecutionTime = 0;
                        
                // Run each test and add up the time of each one so the average can be found
                for (int i = 0; i < testNumbers; i++) {
                    //@TODO: Copy the program so it actually goes through the whole process each time and can resolve properly
                    Shorty shorty = new Shorty(program, Shorty.Mode.Singular);

                    if (i == 0) {
                        //Find out how many asserts were in the program before the removal - only do on first run
                        foreach (Statement stmt in shorty.asserts.Keys) {
                            assertsBefore += shorty.asserts[stmt].Count;
                        }
                    }

                    Stopwatch sw = new Stopwatch();
                    sw.Start();
                    List<AssertStmt> asserts = shorty.FindUnnecessaryAsserts();
                    sw.Stop();

                    averageExecutionTime += sw.ElapsedMilliseconds;

                    //Gather all other needed information in the first run
                    if (i == 0) {
                        assertsRemoved = asserts.Count;
                    }
                }

                //Calculate average execution time and
                averageExecutionTime = averageExecutionTime/testNumbers;
                assertData.Add(new Tuple<string, int, int, float>(program.FullName, assertsBefore, assertsRemoved, averageExecutionTime));
                tw.WriteLine("{0}, {1}, {2}, {3}", program.FullName, assertsBefore, assertsRemoved, averageExecutionTime);
            }
        }

        public void TestInvariantRemoval()
        {
            tw.WriteLine("Invariant Removal");
            tw.WriteLine("Program Name, Invariants Before, Invariants Removed, Average Execution Time(ms)");

            foreach (Microsoft.Dafny.Program program in programs) {
                Console.WriteLine("\nRemoving invariants from {0}", program.FullName);
                int invariantsBefore = 0;
                int invariantsRemoved = 0;
                float averageExecutionTime = 0;

                for (int i = 0; i < testNumbers; i++) {
                    //@TODO: Copy the program so it actually goes through the whole process each time and can resolve properly
                    Shorty shorty = new Shorty(program, Shorty.Mode.Singular);

                    if (i == 0) {
                        //Find out how many invariants were in the program before the removal - only do on first run
                        foreach (LoopStmt stmt in shorty.invariants.Keys) {
                            invariantsBefore += shorty.invariants[stmt].Count;
                        }
                    }

                    Stopwatch sw = new Stopwatch();
                    sw.Start();
                    List<MaybeFreeExpression> invariants = shorty.FindRemovableInvariants();
                    sw.Stop();

                    averageExecutionTime += sw.ElapsedMilliseconds;

                    //Gather all other needed information in the first run
                    if (i == 0) {
                        invariantsRemoved = invariants.Count;
                    }
                }

                //Calculate average execution time and
                averageExecutionTime = averageExecutionTime/testNumbers;
                invariantData.Add(new Tuple<string, int, int, float>(program.FullName, invariantsBefore, invariantsRemoved,
                    averageExecutionTime));
                tw.WriteLine("{0}, {1}, {2}, {3}", program.FullName, invariantsBefore, invariantsRemoved, averageExecutionTime);
            }
        }
    }
}
