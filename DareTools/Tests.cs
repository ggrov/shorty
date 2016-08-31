using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.IO;
using System.Reflection;
using NUnit.Framework;
using Microsoft.Dafny;
using Bpl = Microsoft.Boogie;
using Dare;

namespace DareTools
{
    [TestFixture]
    internal class DareTest
    {
        private static void ContractFailureHandler(Object obj, ContractFailedEventArgs args)
        {
            throw new ContractFailedException();
        }

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
            Contract.ContractFailed += ContractFailureHandler;
        }

        private Program GetProgram(string fileName)
        {
            var dir = Path.GetDirectoryName(Assembly.GetExecutingAssembly().Location);
            dir = Directory.GetParent(dir).FullName;
            dir = Directory.GetParent(dir).FullName;
            dir = Directory.GetParent(dir).FullName;
            dir = dir + "\\tests\\" + fileName;
            Console.WriteLine(dir);
            var nameStart = fileName.LastIndexOf('\\') + 1;
            var programName = fileName.Substring(nameStart, fileName.Length - nameStart);

            ModuleDecl module = new LiteralModuleDecl(new DefaultModuleDecl(), null);
            var builtIns = new BuiltIns();
            Parser.Parse(dir, module, builtIns, new Errors(new InvisibleErrorReporter()));

            return new Program(programName, module, builtIns, new InvisibleErrorReporter());
        }

        private DareController GetDareController(Program program)
        {
            return new DareController(program, new OneAtATimeRemover(program));
//            return new Shorty(program, new SimultaneousMethodRemover(program));
        }

        [Test]
        public void AssertRemoval()
        {
            Initialise();
            var program = GetProgram("FindZero.dfy");
            var dareController = GetDareController(program);

            Assert.AreEqual(3, dareController.Asserts.Count);
            Assert.AreEqual(2, dareController.FindRemovableAsserts().Count);
            Assert.AreEqual(1, dareController.Asserts.Count);
            Assert.True(dareController.IsProgramValid());
        }

        [Test]
        public void InvariantRemoval()
        {
            Initialise();
            var program = GetProgram("ListCopy.dfy");
            var dareController = GetDareController(program);

            Assert.AreEqual(4, dareController.Invariants.Count);
            Assert.AreEqual(1, dareController.FindRemovableInvariants().Count);
            Assert.AreEqual(3, dareController.Invariants.Count);
            Assert.True(dareController.IsProgramValid());
        }

        [Test]
        public void DecreasesRemoval()
        {
            Initialise();
            var program = GetProgram("Combinators.dfy");
            var dareController = GetDareController(program);

            int count = dareController.Decreases.Count;
            foreach (var wildCardDecreasese in dareController.DecreasesWildCards) {
                count += wildCardDecreasese.Count;
            }
            Assert.AreEqual(5, count);
            Assert.AreEqual(1, dareController.FindRemovableDecreases().Count);
            Assert.True(dareController.IsProgramValid());

            int newCount = dareController.Decreases.Count;
            foreach (var wildCardDecreasese in dareController.DecreasesWildCards) {
                newCount += wildCardDecreasese.Count;
            }
            Assert.AreEqual(4, newCount);
        }

        [Test]
        public void LemmaCallRemoval()
        {
            Initialise();
            var program = GetProgram("Streams.dfy");
            var dareController = GetDareController(program);

            Assert.AreEqual(21, dareController.LemmaCalls.Count);
            Assert.AreEqual(17, dareController.FindRemovableLemmaCalls().Count);
            Assert.AreEqual(4, dareController.LemmaCalls.Count);
            Assert.True(dareController.IsProgramValid());
        }

        [Test]
        public void SimplifyAsserts()
        {
            Initialise();
            var program = GetProgram("CombinedAsserts.dfy");
            var dareController = GetDareController(program);

            var simplifiedAsserts = dareController.GetSimplifiedAsserts();
            Assert.AreEqual(1, simplifiedAsserts.Count);
            Assert.True(dareController.IsProgramValid());
            var assert = (AssertStmt) simplifiedAsserts[0].Item2;
            Assert.True(assert.Expr is ParensExpression);
            Assert.True(dareController.IsProgramValid());
            //TODO looking into the assertStmt to make sure it actually broke down
        }

        [Test]
        public void SimplifyInvariants()
        {
            Initialise();
            var program = GetProgram("ListCopy.dfy");
            var dareController = GetDareController(program);

            var simplifiedInvariants = dareController.GetSimplifiedInvariants();
            Assert.AreEqual(1, simplifiedInvariants.Count);
            Assert.True(dareController.IsProgramValid());
        }

        [Test]
        public void TestCalcStatements()
        {
            Initialise();
            var program = GetProgram("Calc.dfy");
            var dareController = GetDareController(program);

            var removedCalcs = dareController.FindRemovableCalcs();

            using (TextWriter tw = File.CreateText("H:\\dafny\\calc.dfy"))
            {
                dareController.PrintProgram(tw);
            }

            Assert.AreEqual(3, removedCalcs.Item1.Count);
            Assert.AreEqual(1, removedCalcs.Item2.Count);
            Assert.AreEqual(1, removedCalcs.Item4.Count);
            Assert.True(dareController.IsProgramValid());
        }

        [Test]
        public void TestMethodRemoval()
        {
            Initialise();
            var program = GetProgram("ListCopy.dfy");
            var members = GetMembers(program);
            foreach (var member in members) {
                if (member.Name == "Copy") {
                    var methodRemover = new MethodRemover(program);
                    var removables = methodRemover.FullSimplify(member);
                    Assert.AreEqual(2, removables.RemovableInvariants.Count);
                    Assert.AreEqual(3, removables.RemovableAsserts.Count);
                    var verifier = new SimpleVerifier();
                    Assert.True(verifier.IsProgramValid(program));
                }
            }
        }

        private List<MemberDecl> GetMembers(Program program)
        {
            var members = new List<MemberDecl>();
            members.AddRange(((ClassDecl) program.DefaultModuleDef.TopLevelDecls[0]).Members);
            return members;
        }

        [Test]
        public void TestSimultaneousAllTypeRemoverConjunctions()
        {
            Initialise();
            var program = GetProgram("ListCopy.dfy");
            
            var dareController = GetDareController(SimpleCloner.CloneProgram(program));
            var data = dareController.FastRemoveAllRemovables();
            Assert.AreEqual(1, data.SimplifiedInvariants.Count);
        }

        [Test]
        public void TestSimultaneousAllTypeRemoverCalcs() {
            Initialise();
            var program = GetProgram("Calc.dfy");
            var dareController = GetDareController(program);

            var data = dareController.FastRemoveAllRemovables();
            var simplifiedCalcs = data.SimplifiedCalcs;
            var removedCalcs = data.RemovableCalcs;

            bool wayOne = simplifiedCalcs.Item1.Count == 3 && simplifiedCalcs.Item2.Count == 1;
            bool wayTwo = simplifiedCalcs.Item1.Count == 2 && simplifiedCalcs.Item2.Count == 2;

            Assert.True(wayOne || wayTwo);
            Assert.AreEqual(1, removedCalcs.Count);
            Assert.True(dareController.IsProgramValid());
        }

        [Test]
        public void TestDifferentRemovals()
        {
            Initialise();
            CompareAllRemovals(GetProgram("Calc.dfy"));
        }

        [Test] [Ignore("Takes a very long time")]
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

            var oneAtATime = new DareController(oneAtATimeProg, new OneAtATimeRemover(oneAtATimeProg));
            var simultaneous = new DareController(simulProg, new SimultaneousMethodRemover(simulProg));
            var allType = new DareController(SimpleCloner.CloneProgram(program));
            var allRemovableTypeResults = allType.FastRemoveAllRemovables();

            var asserts = oneAtATime.FindRemovableAsserts();
            var invariants = oneAtATime.FindRemovableInvariants();
            var decreases = oneAtATime.FindRemovableDecreases();
            var lemmaCalls = oneAtATime.FindRemovableLemmaCalls();
            var simplifiedAsserts = oneAtATime.GetSimplifiedAsserts();
            var simplifiedInvariants = oneAtATime.GetSimplifiedInvariants();

            var simAsserts = simultaneous.FindRemovableAsserts();
            var simInvariants = simultaneous.FindRemovableInvariants();
            var simDecreases = simultaneous.FindRemovableDecreases();
            var simLemmaCalls = simultaneous.FindRemovableLemmaCalls();
            var simSimplifiedAsserts = simultaneous.GetSimplifiedAsserts();
            var simSimplifiedInvariants = simultaneous.GetSimplifiedInvariants();
            var oaatRemovedCalcs = oneAtATime.FindRemovableCalcs();
            var simulRemovedCalcs = simultaneous.FindRemovableCalcs();

            Assert.True(oneAtATime.IsProgramValid());
            Assert.True(simultaneous.IsProgramValid());
            Assert.True(allType.IsProgramValid());

            Assert.AreEqual(asserts.Count, simAsserts.Count);
            Assert.AreEqual(asserts.Count, allRemovableTypeResults.RemovableAsserts.Count);


            Assert.AreEqual(invariants.Count, simInvariants.Count);
            Assert.AreEqual(invariants.Count, allRemovableTypeResults.RemovableInvariants.Count);

            Assert.AreEqual(decreases.Count, simDecreases.Count);
            Assert.AreEqual(decreases.Count, allRemovableTypeResults.RemovableDecreases.Count);

            Assert.AreEqual(lemmaCalls.Count, simLemmaCalls.Count);
            Assert.AreEqual(lemmaCalls.Count, allRemovableTypeResults.RemovableLemmaCalls.Count);

            Assert.AreEqual(simplifiedAsserts.Count, simSimplifiedAsserts.Count);
            Assert.AreEqual(simplifiedAsserts.Count, allRemovableTypeResults.SimplifiedAsserts.Count);

            Assert.AreEqual(simplifiedInvariants.Count, simSimplifiedInvariants.Count);
            Assert.AreEqual(simplifiedInvariants.Count, allRemovableTypeResults.SimplifiedInvariants.Count);

            var allTypeCalcs = allRemovableTypeResults.SimplifiedCalcs;
            Assert.AreEqual(oaatRemovedCalcs.Item1.Count, simulRemovedCalcs.Item1.Count);
            Assert.AreEqual(oaatRemovedCalcs.Item1.Count, allTypeCalcs.Item1.Count);
            Assert.AreEqual(oaatRemovedCalcs.Item2.Count, simulRemovedCalcs.Item2.Count);
            Assert.AreEqual(oaatRemovedCalcs.Item2.Count, allTypeCalcs.Item2.Count);
            Assert.AreEqual(oaatRemovedCalcs.Item3.Count, simulRemovedCalcs.Item3.Count);
            Assert.AreEqual(oaatRemovedCalcs.Item3.Count, allTypeCalcs.Item3.Count);
            Assert.AreEqual(oaatRemovedCalcs.Item4.Count, simulRemovedCalcs.Item4.Count);
            Assert.AreEqual(oaatRemovedCalcs.Item4.Count, allRemovableTypeResults.RemovableCalcs.Count);
        }

        [Test]
        public void ExternalProgramTest()
        {
            Initialise();
            var stop = new StopChecker();
            var dare = new Dare.Dare(stop);
            var program = GetProgram("Combinators.dfy");

            var results = dare.ProcessProgram(program);
        }
    }
}
