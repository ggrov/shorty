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

            Assert.AreEqual(3, shorty.Asserts.Count);
            Assert.AreEqual(2, shorty.FindRemovableAsserts().Count);
            Assert.AreEqual(1, shorty.Asserts.Count);
        }

        [Test]
        public void InvariantRemoval()
        {
            Initialise();
            Program program = GetProgram("ListCopy.dfy");
            Shorty shorty = new Shorty(program);

            Assert.AreEqual(6, shorty.Invariants.Count);
            Assert.AreEqual(2, shorty.FindRemovableInvariants().Count);
            Assert.AreEqual(4, shorty.Invariants.Count);
        }

        [Test]
        public void DecreasesRemoval()
        {
            Initialise();
            Program program = GetProgram("Combinators.dfy");
            Shorty shorty = new Shorty(program);

            Assert.AreEqual(4, shorty.Decreases.Count + shorty.DecreasesWildCards.Count);
            Assert.AreEqual(1, shorty.FindRemovableDecreases().Count);
            Assert.AreEqual(3, shorty.Decreases.Count + shorty.DecreasesWildCards.Count);
        }

        [Test]
        public void LemmaCallRemoval()
        {
            Initialise();
            Program program = GetProgram("Streams.dfy");
            Shorty shorty = new Shorty(program);

            Assert.AreEqual(21, shorty.LemmaCalls.Count);
            Assert.AreEqual(17, shorty.FindRemovableLemmaCalls().Count);
            Assert.AreEqual(4, shorty.LemmaCalls.Count);
        }

        [Test]
        public void SimplifyAsserts()
        {
            Initialise();
            Program program = GetProgram("CombinedAsserts.dfy");
            Shorty shorty = new Shorty(program);

            List<Tuple<AssertStmt, AssertStmt>> simplifiedAsserts = shorty.GetSimplifiedAsserts();
            Assert.AreEqual(1, simplifiedAsserts.Count);
            //TODO looking into the assertStmt to make sure it actually broke down
        }
    }
}
