using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using Microsoft.Dafny;
using NUnit.Framework.Interfaces;

namespace shorty
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
            tw.WriteLine("Program name, OneAtATimeRemover (ms), SimultaneousRemover (ms), AllTypeSimultaneousRemover (ms)");
            List<TimeResults> results = new List<TimeResults>();
            foreach (var program in _programs) {
                try {
                    Console.WriteLine("Comparing "+program.Name);
                    var timeComparer = new TimeComparer(program);
                    var result = timeComparer.CompareTimes(_numberOfRuns);
                    tw.WriteLine("{0},{1},{2},{3}", program.Name, result.Oaat, result.Simul, result.AllType);
                    results.Add(result);
                }
                catch {
                    // ignored
                }
            }
            var avgResults = TimeResults.GetAverageResults(results);
            tw.WriteLine("Average,{0},{1},{2}", avgResults.Oaat, avgResults.Simul, avgResults.AllType);
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
            List<TimeResults> timeResults = new List<TimeResults>();

            for (int i = 0; i < numberOfRuns; i++) {
                timeResults.Add(Compare());
            }

            return TimeResults.GetAverageResults(timeResults);
        }



        private TimeResults Compare()
        {
            var ooatProgram = SimpleCloner.CloneProgram(_program);
            var oaat = new Shorty(ooatProgram, new OneAtATimeRemover(ooatProgram));

            var simulProgram = SimpleCloner.CloneProgram(_program);
            var simul = new Shorty(simulProgram, new SimultaneousMethodRemover(simulProgram));

            var allTypeProgram = SimpleCloner.CloneProgram(_program);
            var allType = new Shorty(allTypeProgram);

            TimeResults timeResults = new TimeResults();

            timeResults.Oaat = GetRemovalTime(oaat);
            timeResults.Simul = GetRemovalTime(simul);

            var stopwatch = new Stopwatch();
            stopwatch.Start();
            allType.FastRemoveAllRemovables(new StopChecker());
            stopwatch.Stop();
            timeResults.AllType = stopwatch.ElapsedMilliseconds;

            return timeResults;
        }

        private long GetRemovalTime(Shorty shorty)
        {
            var stopwatch = new Stopwatch();
            stopwatch.Start();

            shorty.FindRemovableAsserts();
            shorty.FindRemovableInvariants();
            shorty.FindRemovableDecreases();
            shorty.FindRemovableLemmaCalls();
            shorty.GetSimplifiedAsserts();
            shorty.GetSimplifiedInvariants();
            shorty.FindRemovableCalcs();

            stopwatch.Stop();
            return stopwatch.ElapsedMilliseconds;
        }
    }

    class TimeResults
    {
        public long Oaat { get; set; }
        public long Simul { get; set; }
        public long AllType { get; set; }

        public static TimeResults GetAverageResults(List<TimeResults> timeResults)
        {
            var numberOfRuns = timeResults.Count;
            var avgResults = new TimeResults();
            foreach (var result in timeResults) {
                avgResults.Oaat += result.Oaat;
                avgResults.Simul += result.Simul;
                avgResults.AllType += result.AllType;
            }

            avgResults.Oaat /= numberOfRuns;
            avgResults.Simul /= numberOfRuns;
            avgResults.AllType /= numberOfRuns;

            return avgResults;
        }
    }
}
