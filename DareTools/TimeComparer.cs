using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using Microsoft.Dafny;
using Dare;


namespace DareTools
{
    class TimeComparers
    {
        private readonly List<Program> _programs;
        private readonly int _numberOfRuns;

        public TimeComparers(List<Program> programs, int numberOfRuns)
        {
            _programs = programs;
            _numberOfRuns = numberOfRuns;
        }

        public void CompareTimes(TextWriter tw)
        {
            tw.WriteLine("Program name, OneAtATimeRemover (ms), CompleteRemover (ms), AllTypeSimultaneousRemover (ms)");
            List<TimeResults> results = new List<TimeResults>();
            foreach (var program in _programs) {
                try {
                    Console.WriteLine("Comparing " + program.Name);
                    var timeComparer = new TimeComparer(program);
                    var result = timeComparer.CompareTimes(_numberOfRuns);
                    tw.WriteLine("{0},{1},{2},{3}", program.Name, result.Oaat, result.Complete, result.AllType);
                    results.Add(result);
                }
                catch (NotValidException) {
                    Console.WriteLine("Program {0} was not valid at initialisation", program.Name);
                }
                catch (Exception e){
                    Console.WriteLine("Program {0} failed: {1}", program.Name, e.Message);
                }
            }
            var avgResults = TimeResults.GetAverageResults(results);
            tw.WriteLine("Average,{0},{1},{2}", avgResults.Oaat, avgResults.Complete, avgResults.AllType);
        }
    }

    class TimeComparer
    {
        private readonly Program _program;

        public TimeComparer(Program program)
        {
            _program = program;
        }


        public TimeResults CompareTimes(int numberOfRuns = 3)
        {
            var timeResults = new List<TimeResults>();
            for (int i = 0; i < numberOfRuns; i++)
                timeResults.Add(Compare());
            
            return TimeResults.GetAverageResults(timeResults);
        }



        private TimeResults Compare()
        {
            var timeResults = new TimeResults();
            timeResults.Oaat = GetOaatTime();
            timeResults.AllType = GetParallelRemovalTime();
            timeResults.Complete = GetCompleteDareTime();
            return timeResults;
        }

        private long GetParallelRemovalTime() {
            var allTypeProgram = SimpleCloner.CloneProgram(_program);
            var allType = new DareController(allTypeProgram);
            var stopwatch = new Stopwatch();
            stopwatch.Start();
            allType.FastRemoveAllRemovables(new StopChecker());
            stopwatch.Stop();
            return stopwatch.ElapsedMilliseconds;
        }

        private long GetCompleteDareTime() {
            Stopwatch stopwatch = new Stopwatch();
            var completeDareProgram = SimpleCloner.CloneProgram(_program);
            var dareController = new DareController(completeDareProgram);
            stopwatch.Start();
            var removalOrderTesterAssert = new RemovalOrderTester<Statement>(dareController.AllRemovableTypes.GetAssertDictionary(), completeDareProgram);
            removalOrderTesterAssert.TestDifferentRemovals();
            var removalOrderTesterInvar = new RemovalOrderTester<MaybeFreeExpression>(dareController.AllRemovableTypes.GetInvariantDictionary(), completeDareProgram);
            removalOrderTesterInvar.TestDifferentRemovals();
            var removalOrderTesterLemmaCall = new RemovalOrderTester<Statement>(dareController.AllRemovableTypes.GetLemmaCallDictionary(), completeDareProgram);
            removalOrderTesterLemmaCall.TestDifferentRemovals();
            var removalOrderTesterDecreases = new RemovalOrderTester<Expression>(dareController.AllRemovableTypes.GetDecreasesDictionary(), completeDareProgram);
            removalOrderTesterDecreases.TestDifferentRemovals();
            var removalOrderTesterCalc = new RemovalOrderTester<Statement>(dareController.AllRemovableTypes.GetCalcDictionary(), completeDareProgram);
            removalOrderTesterCalc.TestDifferentRemovals();
            stopwatch.Stop();
            return stopwatch.ElapsedMilliseconds;
        }

        private long GetOaatTime()
        {
            var ooatProgram = SimpleCloner.CloneProgram(_program);
            var dareController = new DareController(ooatProgram, new OneAtATimeRemover(ooatProgram));
            var stopwatch = new Stopwatch();
            stopwatch.Start();
            dareController.FindRemovableAsserts();
            dareController.FindRemovableInvariants();
            dareController.FindRemovableDecreases();
            dareController.FindRemovableLemmaCalls();
            dareController.GetSimplifiedAsserts();
            dareController.GetSimplifiedInvariants();
            dareController.FindRemovableCalcs();

            stopwatch.Stop();
            return stopwatch.ElapsedMilliseconds;
        }
    }

    class TimeResults
    {
        public long Oaat { get; set; }
        public long AllType { get; set; }
        public long Complete { get; set; }

        public static TimeResults GetAverageResults(List<TimeResults> timeResults)
        {
            var numberOfRuns = timeResults.Count;
            var avgResults = new TimeResults();
            foreach (var result in timeResults) {
                avgResults.Oaat += result.Oaat;
                avgResults.AllType += result.AllType;
                avgResults.Complete += result.Complete;
            }
            avgResults.Oaat /= numberOfRuns;
            avgResults.AllType /= numberOfRuns;
            avgResults.Complete /= numberOfRuns;
            return avgResults;
        }
    }
}
