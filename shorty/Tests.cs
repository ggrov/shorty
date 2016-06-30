using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reflection;
using System.Text;
using System.Threading.Tasks;
using NUnit.Framework;
using Microsoft.Dafny;
using Bpl = Microsoft.Boogie;

namespace shorty
{
    [TestFixture]
    class ShortyTest
    {
        private void Initialise()
        {
            DafnyOptions.Install(new DafnyOptions());
            Bpl.CommandLineOptions.Clo.Z3ExecutablePath = "H:\\dafny\\repos\\tacny\\tacny\\Binaries\\z3.exe";
//            Bpl.CommandLineOptions.Clo.Z3ExecutablePath = "C:\\users\\Duncan\\Documents\\tacny\\tacny\\Binaries\\z3.exe";
            Bpl.CommandLineOptions.Clo.ApplyDefaultOptions();
            Bpl.CommandLineOptions.Clo.VerifySnapshots = 1;
            Bpl.OutputPrinter printer = new Bpl.ConsolePrinter();
            Bpl.ExecutionEngine.printer = printer;
        }
        private Program GetProgram(string fileName)
        {
            string dir = Path.GetDirectoryName(Assembly.GetExecutingAssembly().Location);
            dir = Directory.GetParent(dir).FullName;
            dir = Directory.GetParent(dir).FullName;
            dir = Directory.GetParent(dir).FullName;
            dir = dir + "\\tests\\" + fileName;
            Console.WriteLine(dir);
            int nameStart = fileName.LastIndexOf('\\') + 1;
            string programName = fileName.Substring(nameStart, fileName.Length - nameStart);

            ModuleDecl module = new LiteralModuleDecl(new DefaultModuleDecl(), null);
            var builtIns = new BuiltIns();
            Parser.Parse(dir, module, builtIns, new Errors(new ConsoleErrorReporter()));

            return new Program(programName, module, builtIns, new ConsoleErrorReporter());
        }

        [Test]
        public void AssertRemoval()
        {
            Initialise();
            Program program = GetProgram("FindZero.dfy");
            Shorty shorty = new Shorty(program);

            // Count asserts before
            int numberOfAsserts = shorty.Asserts.Count;
//            foreach (var method in shorty.Asserts.Keys) {
//                foreach (var block in shorty.Asserts[method].Keys) {
//                    numberOfAsserts += shorty.Asserts[method][block].Count;
//                }
//            }
            Assert.AreEqual(2, numberOfAsserts);
            //Number that are removed
            Assert.AreEqual(1, shorty.FindRemovableAsserts().Count);
        }

        [Test]
        public void InvariantRemoval()
        {
            Initialise();
            Program program = GetProgram("ListCopy.dfy");
            Shorty shorty = new Shorty(program);

            Assert.AreEqual(2, shorty.FindRemovableInvariants().Count);
        }

        [Test]
        public void DecreasesRemoval()
        {
            Initialise();
            Program program = GetProgram("Combinators.dfy");
            Shorty shorty = new Shorty(program);

            List<Expression> removableDecreases = shorty.FindRemoveableDecreases();

            Assert.AreEqual(0, removableDecreases.Count);
        }

        [Test]
        public void LemmaCallRemoval()
        {
            Initialise();
            Program program = GetProgram("Streams.dfy");
            Shorty shorty = new Shorty(program);

            List<UpdateStmt> lemmaCalls = shorty.FindRemovableLemmaCalls();
            Assert.AreEqual(8, lemmaCalls.Count);
        }

        [Test]
        public void SimplifyAsserts()
        {
            Initialise();
            Program program = GetProgram("CombinedAsserts.dfy");
            Shorty shorty = new Shorty(program);

            List<Tuple<AssertStmt, AssertStmt>> simplifiedAsserts = shorty.GetSimplifiedAsserts();
            Assert.AreEqual(1, simplifiedAsserts.Count);
            //TODO more asserts looking into the assertStmt
        }
    }
}
