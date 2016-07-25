using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.Diagnostics.Eventing.Reader;
using System.IO;
using System.Linq;
using System.Net;
using System.Text;
using System.Threading.Tasks;
using Microsoft.Dafny;
using Bpl = Microsoft.Boogie;

namespace shorty
{
    class ShortyMain
    {
        public static void RunLogger(List<Program> programs)
        {
            var logger = new Logger("H:\\dafny\\experimentResults", programs, 3, true);
//                Logger logger = new Logger("C:\\users\\Duncan\\Documents\\dafny\\experimentResults", programs, 1, false);
            logger.LogAllData();
        }

        public static void CompareSearchStrategies(List<Program> programs)
        {
            int numberOfRuns = 5;

            var times = new List<Tuple<Program, long, long>>();
            foreach (var program in programs) {
                var sw = new Stopwatch();
                Shorty shorty = null;
                var valid = true;
                long simple = 0;
                for (var i = 0; i < numberOfRuns; i++) {
                    try {
                        shorty = new Shorty(SimpleCloner.CloneProgram(program));
                        sw.Start();
                        shorty.FindRemovableAsserts();
                        shorty.FindRemovableInvariants();
                        shorty.FindRemovableDecreases();
                        shorty.FindRemovableLemmaCalls();
                        shorty.FindRemovableCalcs(new CalcRemover(program));
                        shorty.GetSimplifiedAsserts();
                        shorty.GetSimplifiedInvariants();
                        sw.Stop();
                        simple += sw.ElapsedMilliseconds;
                        sw.Reset();
                    }
                    catch {
                        valid = false;
                        break;
                    }
                }
                if(!valid) continue;
                long simul = 0;
                for (var i = 0; i < numberOfRuns; i++) {
                    try {
                        var clone = SimpleCloner.CloneProgram(program);
                        shorty = new Shorty(clone, new SimultaneousMethodRemover(clone));
                        sw.Start();
                        shorty.FindRemovableAsserts();
                        shorty.FindRemovableInvariants();
                        shorty.FindRemovableDecreases();
                        shorty.FindRemovableLemmaCalls();
                        shorty.FindRemovableCalcs(new CalcRemover(program));
                        shorty.GetSimplifiedAsserts();
                        shorty.GetSimplifiedInvariants();
                        sw.Stop();
                        simul += sw.ElapsedMilliseconds;
                        sw.Reset();
                    }
                    catch {
                        valid = false;
                        break;
                    }
                }
                if(!valid) continue;
                
                times.Add(new Tuple<Program, long, long>(program, simple/numberOfRuns, simul/numberOfRuns));
            }

            foreach (var tuple in times) {
                Console.WriteLine("{0}: Simple - {1}, Simultaneous - {2}",tuple.Item1, tuple.Item2, tuple.Item3);
            }
        }

        public static void RunTest(List<Program> programs)
        {
            using (TextWriter writer = File.CreateText("H:\\dafny\\results.txt")) {
//            using (TextWriter writer = File.CreateText("C:\\users\\Duncan\\Documents\\results.txt")) {
                var betterSolutionFound = false;
                var programNumber = 1;
                foreach (var program in programs) {
                    Console.WriteLine("Testing {0} | {1}/{2}", program.Name, programNumber++, programs.Count);
                    writer.WriteLine();
                    writer.WriteLine(program.Name);
                    writer.WriteLine();

                    try {
                        var shorty = new Shorty(program);
                        var assertSolutions = shorty.TestDifferentAssertRemovals();
                        var invariantSolutions = shorty.TestDifferentInvariantRemovals();

                        writer.WriteLine("ASSERTS for " + program.Name);
                        writer.WriteLine();

                        betterSolutionFound = PrintResults(assertSolutions, writer, betterSolutionFound);

                        writer.WriteLine();
                        writer.WriteLine("INVARIANTS for " + program.Name);
                        writer.WriteLine();

                        betterSolutionFound = PrintResults(invariantSolutions, writer, betterSolutionFound) || betterSolutionFound;
                    }
                    catch (NotValidException e) {
                        writer.WriteLine("Program " + program.Name + "was not valid: " + e.Message);
                    }
                    catch {
                        //ignore
                    }
                }
                writer.WriteLine(betterSolutionFound ? "\nA better solution was found!" : "\nNo better solution was found");
            }
        }

        private static bool PrintResults<T>(Dictionary<Method, List<List<T>>> solutions, TextWriter writer, bool betterSolutionFound)
        {
            foreach (var method in solutions.Keys) {
                var i = 0;
                var firstValue = solutions[method][i].Count;
                if (firstValue == 0) continue;
                writer.WriteLine("Method: " + method.Name + " | Initial value: " + firstValue);
                foreach (var asserts in solutions[method]) {
                    if (i++ == 0) continue;
                    writer.Write("Solution " + i++ + " | length " + asserts.Count);
                    if (asserts.Count >= firstValue && i > 1) {
                        writer.WriteLine(" | BETTER OR SAME AS FIRST! ({0} >= {1})", asserts.Count, firstValue);
                        betterSolutionFound = true;
                    }
                    else
                        writer.WriteLine();
                }
            }
            return betterSolutionFound;
        }

        public static void ContractFailureHandler(Object obj, ContractFailedEventArgs args)
        {
            throw new ContractFailedException();
        }

        private static void Main(string[] args)
        {
            Contract.Requires(args != null);
            //Setup environment
            DafnyOptions.Install(new DafnyOptions());
            Bpl.CommandLineOptions.Clo.ApplyDefaultOptions();
            DafnyOptions.O.Z3ExecutablePath = "H:\\dafny\\repos\\tacny\\tacny\\Binaries\\z3.exe";
//            DafnyOptions.O.Z3ExecutablePath = "C:\\users\\Duncan\\Documents\\tacny\\tacny\\Binaries\\z3.exe";
            DafnyOptions.O.ApplyDefaultOptions();
            DafnyOptions.O.RunningBoogieFromCommandLine = true;
            DafnyOptions.O.VerifySnapshots = 1;
            DafnyOptions.O.ErrorTrace = 0;
            DafnyOptions.O.ProverKillTime = 10;
            ErrorReporter reporter = new InvisibleErrorReporter();
            Bpl.ExecutionEngine.printer = new InvisibleConsolePrinter();
            Contract.ContractFailed += ContractFailureHandler;


            //string[ filename = new string[args.Length];
            var dafnyPrograms = new List<Program>();

            var fileNames = new List<string>();

            //Check for * directories
            foreach (var fileName in args) {
                if (fileName.EndsWith("\\*") || fileName.EndsWith("/*")) {
                    var newFileNames = Directory.GetFiles(fileName.Substring(0, fileName.Length - 1));
                    foreach (var newFileName in newFileNames) {
                        if (newFileName.EndsWith(".dfy"))
                            fileNames.Add(newFileName);
                    }
                }
                else if (fileName.EndsWith(".dfy")) {
                    fileNames.Add(fileName);
                }
                else {
                    Console.WriteLine(fileName + " not recognised.");
                }
            }

            foreach (var fileName in fileNames) {
                Console.WriteLine("Filename: " + fileName);

                if (!fileName.EndsWith(".dfy")) {
                    Console.WriteLine("Error: file must be a .dfy file");
                    continue;
                }


                //create program from file
                var nameStart = fileName.LastIndexOf('\\') + 1;
                var programName = fileName.Substring(nameStart, fileName.Length - nameStart);

                ModuleDecl module = new LiteralModuleDecl(new DefaultModuleDecl(), null);
                var builtIns = new BuiltIns();
                Parser.Parse(fileName, module, builtIns, new Errors(reporter));

                dafnyPrograms.Add(new Microsoft.Dafny.Program(programName, module, builtIns, reporter));
            }

            Console.WriteLine("1: standard run\n2: run logger\n3: run order testing\n");
            var input = Console.ReadLine();
            int ans;
            if (!Int32.TryParse(input, out ans)) {
                return;
            }
            if (ans < 1 || ans > 4) {
                return;
            }

            switch (ans) {
                case 2:
                    RunLogger(dafnyPrograms);
                    Console.WriteLine("\n\nLogging Complete");
                    Console.ReadLine();
                    return;
                case 3:
                    RunTest(dafnyPrograms);
                    Console.WriteLine("\n\nTests Complete");
                    Console.ReadLine();
                    return;
                case 4:
                    CompareSearchStrategies(dafnyPrograms);
                    Console.ReadLine();
                    return;
            }

            //setup shorty and test the files
            var removeableAsserts = new Dictionary<Program, List<Statement>>();
            var removeableInvariants = new Dictionary<Program, List<MaybeFreeExpression>>();
            var removeableDecreases = new Dictionary<Program, List<Expression>>();
            var removableLemmaCalls = new Dictionary<Program, List<Statement>>();
            var failedInitialValidationPrograms = new List<Program>();
            var failedAssertRemovalPrograms = new List<Program>();

            // Time analysis
            var times = new Dictionary<Program, long>();
            var sw = new Stopwatch();

            // Run all the programs
            foreach (var program in dafnyPrograms) {
                sw.Reset();
                sw.Start();
                Shorty shorty = null;
                try {
                    shorty = new Shorty(program);
                }
                catch (NotValidException e) {
                    Console.WriteLine("Initial failed");
                    failedInitialValidationPrograms.Add(program);
                    continue;
                }

                Console.WriteLine(program.FullName);
                Console.WriteLine("Finding unnecesary asserts");
                var calcs = shorty.FindRemovableCalcs();
                if (!shorty.IsProgramValid()) {
                    throw new NotValidException();
                }

                Console.WriteLine("Finding unnecesary asserts");
                var asserts = shorty.FindRemovableAsserts();
                shorty.GetSimplifiedAsserts();
                if (!shorty.IsProgramValid()) {
                    throw new NotValidException();
                }

                Console.WriteLine("Finding unnecessary loop invariants");
                var invariants = shorty.FindRemovableInvariants();
                if (!shorty.IsProgramValid()) {
                    throw new NotValidException();
                }

                Console.WriteLine("Finding unnecessary loop invariants");
                var decreases = shorty.FindRemovableDecreases();
                if (!shorty.IsProgramValid()) {
                    throw new NotValidException();
                }

                Console.WriteLine("Finding unnecessary lemma calls");
                var lemmaCalls = shorty.FindRemovableLemmaCalls();
                if (!shorty.IsProgramValid()) {
                    throw new NotValidException();
                }

                if (!shorty.IsProgramValid()) {
                    Console.WriteLine("\n\n at end and somehow failed!!!!\n\n");
                    failedInitialValidationPrograms.Add(program);
                }


                //shorty.RemoveAutoGeneratedDecreases();

                removeableAsserts.Add(program, asserts);
                removeableInvariants.Add(program, invariants);
                removeableDecreases.Add(program, decreases);
                removableLemmaCalls.Add(program, lemmaCalls);
                sw.Stop();
                times.Add(program, sw.ElapsedMilliseconds);
                using (TextWriter writer = File.CreateText("H:\\dafny\\programs\\shortied\\short-" + program.FullName)) {
//                using (TextWriter writer = File.CreateText("C:\\users\\Duncan\\Documents\\shortied-" + program.FullName)) {
                    shorty.PrintProgram(writer);
                }
            }

            Console.WriteLine("\n\nRemoveable asserts and invariants for each program:");
            foreach (var program in removeableAsserts.Keys) {
                var time = times[program]/1000f;
                Console.WriteLine(program.FullName + " - running time: " + time + "s ");
                var asserts = "";
                foreach (AssertStmt assert in removeableAsserts[program]) {
                    asserts = (asserts + " (" + assert.Tok.line + "," + assert.Tok.col + "),");
                }
                if (removeableAsserts[program].Count > 0)
                    asserts = "Asserts:" + asserts.Substring(0, asserts.Length - 1); //remove last comma
                else {
                    asserts = "No asserts were removed.";
                }
                var invariants = "";
                foreach (var invariant in removeableInvariants[program]) {
                    invariants = invariants + " (" + invariant.E.tok.line + "," + invariant.E.tok.col + "),";
                }

                if (removeableInvariants[program].Count > 0)
                    invariants = "Invariants:" + invariants.Substring(0, invariants.Length - 1);
                else
                    invariants = "No invariants were removed";

                var decreaseses = "";
                foreach (var decreases in removeableDecreases[program]) {
                    decreaseses = decreaseses + " (" + decreases.tok.line + "," + decreases.tok.col + "),";
                }

                if (removeableDecreases[program].Count > 0)
                    decreaseses = "Decreaseses:" + decreaseses.Substring(0, decreaseses.Length - 1);
                else
                    decreaseses = "No decreaseses were removed";

                var lemmaCalls = "";
                foreach (UpdateStmt update in removableLemmaCalls[program]) {
                    lemmaCalls = lemmaCalls + " (" + update.Tok.line + "," + update.Tok.col + "),";
                }

                if (removableLemmaCalls[program].Count > 0)
                    lemmaCalls = "LemmaCalls:" + lemmaCalls.Substring(0, lemmaCalls.Length - 1);
                else {
                    lemmaCalls = "No lemma calls were removed";
                }

                Console.WriteLine(asserts + "\n");
                Console.WriteLine(invariants + "\n");
                Console.WriteLine(decreaseses + "\n");
                Console.WriteLine(lemmaCalls + "\n");
            }

            Console.WriteLine("\nPrograms that failed initial verification:");
            foreach (var program in failedInitialValidationPrograms) {
                Console.Write(program.FullName + " | ");
            }

            Console.WriteLine("\nPrograms that failed assert removal:");
            foreach (var program in failedAssertRemovalPrograms) {
                Console.Write(program.FullName + " | ");
            }
            Console.Read();
        }
    }

    class InvisibleConsolePrinter : Bpl.ConsolePrinter
    {
        public override void ReportBplError(Bpl.IToken tok, string message, bool error, TextWriter tw, string category = null)
        {
            //tw.WriteLine("Error");
        }

        public new void WriteErrorInformation(Bpl.ErrorInformation errorInfo, TextWriter tw, bool skipExecutionTrace = true)
        {
            //do nothing...
        }
    }

    class ContractFailedException : Exception
    {
        public ContractFailedException() {}
        public ContractFailedException(string message) : base(message) {}
    }

    class InvisibleErrorReporter : ConsoleErrorReporter
    {
        public override bool Message(MessageSource source, ErrorLevel level, Bpl.IToken tok, string msg)
        {
            //return base.Message(source, level, tok, msg);
            return false;
        }
    }
}
