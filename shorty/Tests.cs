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
            Bpl.CommandLineOptions.Clo.ErrorTrace = 0;
            Bpl.OutputPrinter printer = new InvisibleConsolePrinter();
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
            Parser.Parse(dir, module, builtIns, new Errors(new InvisibleErrorReproter()));

            return new Program(programName, module, builtIns, new InvisibleErrorReproter());
        }

        [Test]
        public void AssertRemoval()
        {
            Initialise();
            Program program = GetProgram("FindZero.dfy");
            Shorty shorty = new Shorty(program, new SimultaneousMethodRemover(program));

            Assert.AreEqual(3, shorty.Asserts.Count);
            Assert.AreEqual(2, shorty.FindRemovableAsserts().Count);
            Assert.AreEqual(1, shorty.Asserts.Count);
            Assert.True(shorty.IsProgramValid());
        }

        [Test]
        public void InvariantRemoval()
        {
            Initialise();
            Program program = GetProgram("ListCopy.dfy");
            Shorty shorty = new Shorty(program, new SimultaneousMethodRemover(program));

            Assert.AreEqual(6, shorty.Invariants.Count);
            Assert.AreEqual(1, shorty.FindRemovableInvariants().Count);
            Assert.AreEqual(5, shorty.Invariants.Count);
            Assert.True(shorty.IsProgramValid());
        }

        [Test]
        public void DecreasesRemoval()
        {
            Initialise();
            Program program = GetProgram("Combinators.dfy");
            Shorty shorty = new Shorty(program, new SimultaneousMethodRemover(program));

            Assert.AreEqual(4, shorty.Decreases.Count + shorty.DecreasesWildCards.Count);
            Assert.AreEqual(1, shorty.FindRemovableDecreases().Count);
            Assert.AreEqual(3, shorty.Decreases.Count + shorty.DecreasesWildCards.Count);
            Assert.True(shorty.IsProgramValid());
        }

        [Test]
        public void LemmaCallRemoval()
        {
            Initialise();
            Program program = GetProgram("Streams.dfy");
            Shorty shorty = new Shorty(program, new SimultaneousMethodRemover(program));

            Assert.AreEqual(21, shorty.LemmaCalls.Count);
            Assert.AreEqual(17, shorty.FindRemovableLemmaCalls().Count);
            Assert.AreEqual(4, shorty.LemmaCalls.Count);
            Assert.True(shorty.IsProgramValid());
        }

        [Test]
        public void SimplifyAsserts()
        {
            Initialise();
            Program program = GetProgram("CombinedAsserts.dfy");
            Shorty shorty = new Shorty(program, new SimultaneousMethodRemover(program));

            List<Tuple<Statement, Statement>> simplifiedAsserts = shorty.GetSimplifiedAsserts();
            Assert.AreEqual(1, simplifiedAsserts.Count);
            Assert.True(shorty.IsProgramValid());
            AssertStmt assert = (AssertStmt)simplifiedAsserts[0].Item2;
            Assert.True(assert.Expr is ForallExpr);
            //TODO looking into the assertStmt to make sure it actually broke down
        }

        [Test]
        public void SimplifyInvariants()
        {
            Initialise();
            Program program = GetProgram("ListCopy.dfy");
            Shorty shorty = new Shorty(program, new SimultaneousMethodRemover(program));

            var simplifiedInvariants = shorty.GetSimplifiedInvariants();
            Assert.AreEqual(1, simplifiedInvariants.Count);
            Assert.True(shorty.IsProgramValid());
        }

        [Test]
        public void TestCalcStatements()
        {
            Initialise();
            Program program = GetProgram("Calc.dfy");
            Shorty shorty = new Shorty(program, new OneAtATimeRemover(program));

            var removedCalcs = shorty.FindRemovableCalcs();
//            using (TextWriter writer = File.CreateText("H:\\dafny\\test-" + program.FullName)) {
//                shorty.PrintProgram(writer);
//            }
            Assert.AreEqual(3, removedCalcs.Item1.Count);
            Assert.AreEqual(1, removedCalcs.Item2.Count);
            Assert.AreEqual(1, removedCalcs.Item4.Count);
        }
    }
}
