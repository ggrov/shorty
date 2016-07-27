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
            DafnyOptions.O.ProverKillTime = 10;
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
            Parser.Parse(dir, module, builtIns, new Errors(new InvisibleErrorReporter()));

            return new Program(programName, module, builtIns, new InvisibleErrorReporter());
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

            Assert.AreEqual(5, shorty.Invariants.Count);
            Assert.AreEqual(1, shorty.FindRemovableInvariants().Count);
            Assert.AreEqual(4, shorty.Invariants.Count);
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
            Assert.True(assert.Expr is ParensExpression);
            Assert.True(shorty.IsProgramValid());
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
            Assert.AreEqual(3, removedCalcs.Item1.Count);
            Assert.AreEqual(1, removedCalcs.Item2.Count);
            Assert.AreEqual(1, removedCalcs.Item4.Count);
            Assert.True(shorty.IsProgramValid());
        }

        [Test]
        public void TestDifferentRemovals()
        {
            Initialise();
            CompareAllRemovals(GetProgram("ListCopy.dfy"));
        }

        [Test]//[Ignore("Takes a very long time")]
        public void ThouroughTestDifferentRemovals()
        {
            Initialise();
            CompareAllRemovals(GetProgram("ListCopy.dfy"));
            CompareAllRemovals(GetProgram("Calc.dfy"));
            CompareAllRemovals(GetProgram("CombinedAsserts.dfy"));
            CompareAllRemovals(GetProgram("Combinators.dfy"));
            CompareAllRemovals(GetProgram("FindZero.dfy"));
            CompareAllRemovals(GetProgram("Streams.dfy"));
        }

        private void CompareAllRemovals(Program program)
        {
            var oneAtATimeProg = SimpleCloner.CloneProgram(program);
            var simulProg = SimpleCloner.CloneProgram(program);

            Shorty oneAtATime = new Shorty(oneAtATimeProg, new OneAtATimeRemover(oneAtATimeProg));
            Shorty simultaneous = new Shorty(simulProg, new SimultaneousMethodRemover(simulProg));

            Assert.AreEqual(oneAtATime.FindRemovableAsserts().Count, simultaneous.FindRemovableAsserts().Count);
            Assert.AreEqual(oneAtATime.FindRemovableInvariants().Count, simultaneous.FindRemovableInvariants().Count);
            Assert.AreEqual(oneAtATime.FindRemovableDecreases().Count, simultaneous.FindRemovableDecreases().Count);
            Assert.AreEqual(oneAtATime.FindRemovableLemmaCalls().Count, simultaneous.FindRemovableLemmaCalls().Count);
            var oaatRemovedCalcs = oneAtATime.FindRemovableCalcs();
            var simulRemovedCalcs = simultaneous.FindRemovableCalcs();
            Assert.AreEqual(oaatRemovedCalcs.Item1.Count, simulRemovedCalcs.Item1.Count);
            Assert.AreEqual(oaatRemovedCalcs.Item2.Count, simulRemovedCalcs.Item2.Count);
            Assert.AreEqual(oaatRemovedCalcs.Item3.Count, simulRemovedCalcs.Item3.Count);
            Assert.AreEqual(oaatRemovedCalcs.Item4.Count, simulRemovedCalcs.Item4.Count);
            Assert.AreEqual(oneAtATime.GetSimplifiedAsserts().Count, simultaneous.GetSimplifiedAsserts().Count);
            Assert.AreEqual(oneAtATime.GetSimplifiedInvariants().Count, simultaneous.GetSimplifiedInvariants().Count);
            Assert.True(oneAtATime.IsProgramValid());
            Assert.True(simultaneous.IsProgramValid());
        }
    }
}
