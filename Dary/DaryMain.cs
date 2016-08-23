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

namespace Dary
{
    class DaryMain
    {
        private static readonly ErrorReporter Reporter = new InvisibleErrorReporter();

        private static void Main(string[] args)
        {
            Contract.Requires(args != null);
            SetupEnvironment();
            var dafnyPrograms = GetPrograms(args);

            Console.WriteLine("1: simplify and print\n2: run logger\n3: run order testing\n4: Run Strategy Comparison");
            var input = Console.ReadLine();
            var ans = GetInputAsInt(input);

            switch (ans) {
                case 1:
                    SimplifyAndPrintPrograms(dafnyPrograms);
                    Console.WriteLine("\n\nPrograms printed");
                    break;
                case 2:
                    RunLogger(dafnyPrograms);
                    Console.WriteLine("\n\nLogging Complete");
                    break;
                case 3:
                    RunTest(dafnyPrograms);
                    Console.WriteLine("\n\nTests Complete");
                    break;
                case 4:
                    CompareSearchStrategies(dafnyPrograms);
                    Console.WriteLine("\n\nComparison Completed");
                    break;
                default:
                    Console.WriteLine("Invalid input: " + input);
                    break;
            }
            Console.ReadLine();
        }

        private static int GetInputAsInt(string input)
        {
            int ans;
            if (!int.TryParse(input, out ans)) {
                ans = 0;
            }
            return ans;
        }

        private static List<Program> GetPrograms(string[] args)
        {
            var dafnyPrograms = new List<Program>();
            var fileNames = new List<string>();
            foreach (var arg in args)
                fileNames.AddRange(GetFileNames(arg));

            foreach (var fileName in fileNames) {
                Console.WriteLine("Filename: " + fileName);
                dafnyPrograms.Add(CreateProgramFromFileName(fileName));
            }
            return dafnyPrograms;
        }

        private static Program CreateProgramFromFileName(string fileName)
        {
            var nameStart = fileName.LastIndexOf('\\') + 1;
            var programName = fileName.Substring(nameStart, fileName.Length - nameStart);

            ModuleDecl module = new LiteralModuleDecl(new DefaultModuleDecl(), null);
            var builtIns = new BuiltIns();
            Parser.Parse(fileName, module, builtIns, new Errors(Reporter));

            var program = new Program(programName, module, builtIns, Reporter);
            return program;
        }

        private static List<string> GetFileNames(string arg)
        {
            var fileNames = new List<string>();
            if (arg.EndsWith("\\*") || arg.EndsWith("/*")) {
                var newFileNames = Directory.GetFiles(arg.Substring(0, arg.Length - 1));
                fileNames.AddRange(newFileNames.Where(newFileName => newFileName.EndsWith(".dfy")));
            }
            else if (arg.EndsWith(".dfy")) {
                fileNames.Add(arg);
            }
            else {
                Console.WriteLine(arg + " not recognised.");
            }
            return fileNames;
        }

        private static void SetupEnvironment()
        {
            DafnyOptions.Install(new DafnyOptions());
            Bpl.CommandLineOptions.Clo.ApplyDefaultOptions();
//            DafnyOptions.O.Z3ExecutablePath = "H:\\dafny\\repos\\tacny\\tacny\\Binaries\\z3.exe";
            DafnyOptions.O.Z3ExecutablePath = "C:\\users\\Duncan\\Documents\\tacny\\tacny\\Binaries\\z3.exe";
            DafnyOptions.O.ApplyDefaultOptions();
            DafnyOptions.O.RunningBoogieFromCommandLine = true;
            DafnyOptions.O.VerifySnapshots = 1;
            DafnyOptions.O.ErrorTrace = 0;
            DafnyOptions.O.ProverKillTime = 10;
            Bpl.ExecutionEngine.printer = new InvisibleConsolePrinter();
            Contract.ContractFailed += ContractFailureHandler;
        }

        public static void RunLogger(List<Program> programs)
        {
//            var logger = new Logger("H:\\dafny\\experimentResults", programs, 3, true);
                Logger logger = new Logger("C:\\users\\Duncan\\Documents\\dafny\\experimentResults", programs, 1, false);
            logger.LogAllData();
        }

        public static void CompareSearchStrategies(List<Program> programs)
        {
            using (TextWriter tw = File.CreateText("H:\\dafny\\experimentResults\\SearchStrategyComparisons.csv")) {
                TimeComparers timeComparers = new TimeComparers(programs, 1);
                timeComparers.CompareTimes(tw);
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
                    betterSolutionFound = TestRemovalOrderingOnProgram(program, writer) || betterSolutionFound;
                }
                writer.WriteLine(betterSolutionFound ? "\nA better solution was found!" : "\nNo better solution was found");
            }
        }

        private static bool TestRemovalOrderingOnProgram(Program program, TextWriter writer)
        {
            var betterSolutionFound = false;
            try {
                var daryController = new DaryController(program);
                var assertSolutions = daryController.TestDifferentAssertRemovals();
                var invariantSolutions = daryController.TestDifferentInvariantRemovals();

                writer.WriteLine("ASSERTS for " + program.Name);
                writer.WriteLine();

                betterSolutionFound = PrintResults(assertSolutions, writer);

                writer.WriteLine();
                writer.WriteLine("INVARIANTS for " + program.Name);
                writer.WriteLine();
                betterSolutionFound = PrintResults(invariantSolutions, writer) || betterSolutionFound;
            }
            catch (NotValidException e) {
                writer.WriteLine("Program " + program.Name + "was not valid: " + e.Message);
            }
            catch {
                //ignore
            }
            return betterSolutionFound;
        }

        private static bool PrintResults<T>(Dictionary<Method, List<List<T>>> solutions, TextWriter writer)
        {
            var betterSolutionFound = false;
            foreach (var method in solutions.Keys) {
                var i = 0;
                var firstValue = solutions[method][i].Count;
                if (firstValue == 0) continue;
                writer.WriteLine("Method: " + method.Name + " | Initial value: " + firstValue);
                foreach (var items in solutions[method]) {
                    if (i++ == 0) continue;
                    writer.Write("Solution " + i++ + " | length " + items.Count);
                    if (items.Count >= firstValue && i > 1) {
                        writer.WriteLine(" | BETTER OR SAME AS FIRST! ({0} >= {1})", items.Count, firstValue);
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

        private static void SimplifyAndPrintPrograms(List<Program> dafnyPrograms)
        {
            foreach (var program in dafnyPrograms)
                SimplifyAndPrintProgram(program);
        }

        private static void SimplifyAndPrintProgram(Program program)
        {
            Console.WriteLine("Simplifying " + program.Name);
            try {
                var daryController = new DaryController(program, new OneAtATimeRemover(program));
                daryController.FindRemovableAsserts();
                daryController.FindRemovableInvariants();
                daryController.FindRemovableDecreases();
                daryController.FindRemovableLemmaCalls();
                daryController.FindRemovableCalcs();
                daryController.GetSimplifiedAsserts();
                daryController.GetSimplifiedInvariants();
                using (TextWriter writer = File.CreateText("H:\\dafny\\programs\\shortied\\" + program.Name + ".txt")) {
                    daryController.PrintProgram(writer);
                }
            }
            catch (Exception e) {
                Console.WriteLine(e.Message);
            }
        }
    }

    class InvisibleConsolePrinter : Bpl.ConsolePrinter
    {
        public override void ReportBplError(Bpl.IToken tok, string message, bool error, TextWriter tw, string category = null) {}
        public new void WriteErrorInformation(Bpl.ErrorInformation errorInfo, TextWriter tw, bool skipExecutionTrace = true) {}
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
            return false;
        }
    }
}
