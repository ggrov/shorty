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
        static Bpl.OutputPrinter printer;

        public static void RunLogger(List<Program> programs)
        {
            using (TextWriter writer = File.CreateText("H:\\dafny\\test.csv")) {
//            using (TextWriter writer = File.CreateText("C:\\users\\Duncan\\Documents\\test.csv")) {
                Logger logger = new Logger(writer, programs, 1);
                logger.LogAllData();
            }
        }

        public static void RunTest(List<Program> programs)
        {
            using (TextWriter writer = File.CreateText("H:\\dafny\\results.txt")) {
//            using (TextWriter writer = File.CreateText("C:\\users\\Duncan\\Documents\\results.txt")) {
                bool betterSolutionFound = false;
                foreach (var program in programs) {
                    Shorty shorty = new Shorty(program);
                    Dictionary<Method,List<List<Statement>>> solutions = shorty.TestDifferentAssertRemovals();

                    foreach (Method method in solutions.Keys) {
                        int i = 0;
                        int firstValue = solutions[method][i].Count;
                        writer.WriteLine("Method: "+method.Name);
                        foreach (var asserts in solutions[method]) {
                            writer.Write("Solution " + ++i + " | length " + asserts.Count);
                            if (asserts.Count >= firstValue && i > 1) {
                                writer.WriteLine(" | BETTER OR SAME AS FIRST!!!!!!!!!");
                                betterSolutionFound = true;
                            }
                            else {
                                writer.WriteLine();
                            }
                        }
                    }


                }
                writer.WriteLine(betterSolutionFound ? "A better solution was found!" : "No better solution was found");
            }
        }

        private static void Main(string[] args)
        {
            Contract.Requires(args != null);
            //Setup environment
            DafnyOptions.Install(new DafnyOptions());
            Bpl.CommandLineOptions.Clo.Z3ExecutablePath = "H:\\dafny\\repos\\tacny\\tacny\\Binaries\\z3.exe";
//            Bpl.CommandLineOptions.Clo.Z3ExecutablePath = "C:\\users\\Duncan\\Documents\\tacny\\tacny\\Binaries\\z3.exe";
            Bpl.CommandLineOptions.Clo.ApplyDefaultOptions();
            Bpl.CommandLineOptions.Clo.VerifySnapshots = 1;
            printer = new Bpl.ConsolePrinter();
            //printer.
            Bpl.ExecutionEngine.printer = printer;

            //string[ filename = new string[args.Length];
            List<Program> dafnyPrograms = new List<Program>();

            List<string> fileNames = new List<string>();

            //Check for * directories
            foreach (string fileName in args) {
                if (fileName.EndsWith("\\*") || fileName.EndsWith("/*")) {
                    string[] newFileNames = Directory.GetFiles(fileName.Substring(0, fileName.Length - 1));
                    foreach (string newFileName in newFileNames) {
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

            foreach (string fileName in fileNames) {
                Console.WriteLine("Filename: " + fileName);

                if (!fileName.EndsWith(".dfy")) {
                    Console.WriteLine("Error: file must be a .dfy file");
                    continue;
                }


                //create program from file
                int nameStart = fileName.LastIndexOf('\\') + 1;
                string programName = fileName.Substring(nameStart, fileName.Length - nameStart);

                ModuleDecl module = new LiteralModuleDecl(new DefaultModuleDecl(), null);
                var builtIns = new BuiltIns();
                Parser.Parse(fileName, module, builtIns, new Errors(new ConsoleErrorReporter()));

                dafnyPrograms.Add(new Microsoft.Dafny.Program(programName, module, builtIns, new ConsoleErrorReporter()));
            }

            Console.WriteLine("1: standard run\n2: run logger\n3: run order testing\n");
            string input = Console.ReadLine();
            int ans;
            if (!Int32.TryParse(input, out ans)) {
                return;
            }
            if (ans < 1 || ans > 3) {
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
            }

            //setup shorty and test the files
            Dictionary<Program, List<Statement>> removeableAsserts = new Dictionary<Program, List<Statement>>();
            Dictionary<Program, List<MaybeFreeExpression>> removeableInvariants = new Dictionary<Program, List<MaybeFreeExpression>>();
            Dictionary<Program, List<Expression>> removeableDecreases = new Dictionary<Program, List<Expression>>();
            Dictionary<Program, List<Statement>> removableLemmaCalls = new Dictionary<Program, List<Statement>>();
            List<Program> failedInitialValidationPrograms = new List<Program>();
            List<Program> failedAssertRemovalPrograms = new List<Program>();

            // Time analysis
            Dictionary<Program, long> times = new Dictionary<Program, long>();
            Stopwatch sw = new Stopwatch();

            // Run all the programs
            foreach (Program program in dafnyPrograms) {
                sw.Reset();
                sw.Start();
                var shorty = new Shorty(program);
//                shorty.PrintAsserts();
                Console.WriteLine(program.FullName);
                if (!shorty.IsProgramValid()) {
                    Console.WriteLine("Initial failed");
                    failedInitialValidationPrograms.Add(program);
                    continue;
                }

                Console.WriteLine("Finding unnecesary asserts");
                List<Statement> asserts = shorty.FindRemovableAsserts();
                shorty.GetSimplifiedAsserts();
                if (asserts == null) {
                    Console.WriteLine("Finding unnecessary asserts failed");
                    failedAssertRemovalPrograms.Add(program);
                    continue;
                }

                Console.WriteLine("Finding unnecessary loop invariants");
                List<MaybeFreeExpression> invariants = shorty.FindRemovableInvariants();

                if (invariants == null) {
                    Console.WriteLine("Finding invariants failed");
                    continue;
                }

                Console.WriteLine("Finding unnecessary loop invariants");
                List<Expression> decreases = shorty.FindRemovableDecreases();
                if (decreases == null) {
                    Console.WriteLine("Finding decreases failed");
                    continue;
                }

                Console.WriteLine("Finding unnecessary lemma calls");
                List<Statement> lemmaCalls = shorty.FindRemovableLemmaCalls();
                if (lemmaCalls == null) {
                    Console.WriteLine("Finding lemma calls failed");
                    continue;
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
            foreach (Program program in removeableAsserts.Keys) {
                float time = times[program]/1000f;
                Console.WriteLine(program.FullName + " - running time: " + time + "s ");
                string asserts = "";
                foreach (AssertStmt assert in removeableAsserts[program]) {
                    asserts = (asserts + " (" + assert.Tok.line + "," + assert.Tok.col + "),");
                }
                if (removeableAsserts[program].Count > 0)
                    asserts = "Asserts:" + asserts.Substring(0, asserts.Length - 1); //remove last comma
                else {
                    asserts = "No asserts were removed.";
                }
                string invariants = "";
                foreach (MaybeFreeExpression invariant in removeableInvariants[program]) {
                    invariants = invariants + " (" + invariant.E.tok.line + "," + invariant.E.tok.col + "),";
                }

                if (removeableInvariants[program].Count > 0)
                    invariants = "Invariants:" + invariants.Substring(0, invariants.Length - 1);
                else
                    invariants = "No invariants were removed";

                string decreaseses = "";
                foreach (Expression decreases in removeableDecreases[program]) {
                    decreaseses = decreaseses + " (" + decreases.tok.line + "," + decreases.tok.col + "),";
                }

                if (removeableDecreases[program].Count > 0)
                    decreaseses = "Decreaseses:" + decreaseses.Substring(0, decreaseses.Length - 1);
                else
                    decreaseses = "No decreaseses were removed";

                string lemmaCalls = "";
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
            foreach (Program program in failedInitialValidationPrograms) {
                Console.Write(program.FullName + " | ");
            }

            Console.WriteLine("\nPrograms that failed assert removal:");
            foreach (Program program in failedAssertRemovalPrograms) {
                Console.Write(program.FullName + " | ");
            }
            Console.Read();
        }
    }
}
