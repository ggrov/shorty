using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;
using Microsoft.Dafny;
using Bpl = Microsoft.Boogie;
using Dare;
using DareSim = Dare.Dare;

namespace DareTools
{
    class DareMain
    {
        private static readonly ErrorReporter Reporter = new InvisibleErrorReporter();

        private static string _outputDir;
        private static string _z3Loc;

        //Args - z3.exe location | output directory | dafny programs
        private static void Main(string[] args)
        {
            Contract.Requires(args != null);
            SetupEnvironment();
            var dafnyPrograms = GetPrograms(args);
            if (dafnyPrograms == null) return;

            Console.WriteLine("1: simplify and print\n2: run logger\n3: run order testing\n4: Run Strategy Comparison\n5: Simulate Process Program");
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
                case 5:
                    ProcessPrograms(dafnyPrograms);
                    Console.WriteLine("\n\nProcess Completed Completed");
                    break;
                default:
                    Console.WriteLine("Invalid input: " + input);
                    break;
            }
            Console.ReadLine();
        }

        private static void ProcessPrograms(List<Program> dafnyPrograms)
        {
            SimpleVerifier verifier = new SimpleVerifier();
            DareSim dare = new DareSim(new StopChecker());
            foreach (var program in dafnyPrograms) {
                dare.ProcessProgram(program);
                using (TextWriter writer = File.CreateText(_outputDir + "\\processed-" + program.Name)) {
                    PrintProgram(program, writer);
                }
                if (!verifier.IsProgramValid(program)) {
                    throw new Exception("Program not valid after process");
                }
                var decls = program.DefaultModuleDef.TopLevelDecls;
                var members = new List<MemberDecl>();
                foreach (var topLevelDecl in decls) {
                    var classDec = topLevelDecl as ClassDecl;
                    if(classDec==null) continue;
                    members.AddRange(classDec.Members);
                }
                dare.ProcessMembers(program, members);
            }
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
            if (args.Length < 2) {
                Console.WriteLine("You must enter the location of your z3 executable and your output directory as parameters");
                return null;
            }

            _z3Loc = args[0];
            _outputDir = args[1];

            var files = args.Skip(2).ToArray();

            var dafnyPrograms = new List<Program>();
            var fileNames = new List<string>();
            foreach (var file in files)
                fileNames.AddRange(GetFileNames(file));

            foreach (var fileName in fileNames) {
                Console.WriteLine("Filename: " + fileName);
                dafnyPrograms.Add(CreateProgramFromFileName(fileName));
            }
            Console.WriteLine("Loaded {0} programs",dafnyPrograms.Count);
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
            DafnyOptions.O.Z3ExecutablePath = _z3Loc;
            DafnyOptions.O.ApplyDefaultOptions();
            DafnyOptions.O.RunningBoogieFromCommandLine = true;
            DafnyOptions.O.VerifySnapshots = 1;
            DafnyOptions.O.ErrorTrace = 0;
            DafnyOptions.O.ProverKillTime = 15;
            Bpl.ExecutionEngine.printer = new InvisibleConsolePrinter();
            Contract.ContractFailed += ContractFailureHandler;
        }
        
        public static void RunLogger(List<Program> programs) {
            var testExecTimes = GetTestExecTimes();
            var numTimes = 1;
            if (testExecTimes)
                numTimes = GetNumTimes();

            var logger = new Logger(_outputDir, programs, numTimes, testExecTimes);
            logger.LogAllData();
        }

        private static bool GetTestExecTimes() {
            bool testExecTimes;
            Console.WriteLine("Would you like to test verification times?(y/n)");
            var ans = Console.ReadLine();
            switch (ans) {
                case "y":
                case "Y":
                    testExecTimes = true;
                    break;
                case "n":
                case "N":
                    testExecTimes = false;
                    break;
                default:
                    Console.WriteLine("Invalid input, please enter y or n");
                    return GetTestExecTimes();
            }
            return testExecTimes;
        }

        private static int GetNumTimes() {
            Console.WriteLine("How many times would you like to run each program to analise verification time?");
            try {
                var numTimes = int.Parse(Console.ReadLine());
                return numTimes;
            }
            catch {
                Console.WriteLine("Input wasn't a valid integer number.");
                return GetNumTimes();
            }
        }

        public static void CompareSearchStrategies(List<Program> programs) {
            var numOfRuns = GetNumRuns();
            using (TextWriter tw = File.CreateText(_outputDir+"\\SearchStrategyComparisons.csv")) {
                var timeComparers = new TimeComparers(programs, numOfRuns);
                timeComparers.CompareTimes(tw);
            }
        }

        private static int GetNumRuns() {
            try {
                Console.WriteLine("How many attempts do you want to average the times over?");
                return int.Parse(Console.ReadLine());
            }
            catch {
                Console.WriteLine("Input was invalid - please enter an integer");
                return GetNumRuns();
            }
        }

        public static void RunTest(List<Program> programs)
        {
            using (TextWriter writer = File.CreateText(_outputDir + "\\results.txt"))
            {
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
                var dareController = new DareController(program);

                var removalOrderTesterAssert = new RemovalOrderTester<Statement>(dareController.AllRemovableTypes.GetAssertDictionary(), program);
                var assertSolutions = removalOrderTesterAssert.TestDifferentRemovals();

                var removalOrderTesterInvar = new RemovalOrderTester<MaybeFreeExpression>(dareController.AllRemovableTypes.GetInvariantDictionary(), program);
                var invariantSolutions = removalOrderTesterInvar.TestDifferentRemovals();

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
                var dareController = new DareController(program, new OneAtATimeRemover(program));
                dareController.FastRemoveAllRemovables();

                using (TextWriter writer = File.CreateText(_outputDir + "\\new-" + program.Name)) {
                    PrintProgram(program, writer);
                }
            }
            catch (Exception e) {
                Console.WriteLine(e.Message);
            }
        }

        private static void PrintProgram(Program program, TextWriter writer)
        {
                var dafnyPrinter = new Printer(writer);
                dafnyPrinter.PrintProgram(program, false);
        }
    }
}
