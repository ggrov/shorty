using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.IO;
using System.Reflection;
using NUnit.Framework;
using Microsoft.Dafny;
using Bpl = Microsoft.Boogie;
using Dary;

namespace DaryTools
{
    [TestFixture]
    internal class DaryTest
    {
        private static void ContractFailureHandler(Object obj, ContractFailedEventArgs args)
        {
            throw new ContractFailedException();
        }

        private void Initialise()
        {
            DafnyOptions.Install(new DafnyOptions());
//            Bpl.CommandLineOptions.Clo.Z3ExecutablePath = "H:\\dafny\\repos\\tacny\\tacny\\Binaries\\z3.exe";
            Bpl.CommandLineOptions.Clo.Z3ExecutablePath = "C:\\users\\Duncan\\Documents\\tacny\\tacny\\Binaries\\z3.exe";
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

        private DaryController GetDaryController(Program program)
        {
            return new DaryController(program, new OneAtATimeRemover(program));
//            return new Shorty(program, new SimultaneousMethodRemover(program));
        }

        [Test]
        public void AssertRemoval()
        {
            Initialise();
            var program = GetProgram("FindZero.dfy");
            var daryController = GetDaryController(program);

            Assert.AreEqual(3, daryController.Asserts.Count);
            Assert.AreEqual(2, daryController.FindRemovableAsserts().Count);
            Assert.AreEqual(1, daryController.Asserts.Count);
            Assert.True(daryController.IsProgramValid());
        }

        [Test]
        public void InvariantRemoval()
        {
            Initialise();
            var program = GetProgram("ListCopy.dfy");
            var daryController = GetDaryController(program);

            Assert.AreEqual(4, daryController.Invariants.Count);
            Assert.AreEqual(1, daryController.FindRemovableInvariants().Count);
            Assert.AreEqual(3, daryController.Invariants.Count);
            Assert.True(daryController.IsProgramValid());
        }

        [Test]
        public void DecreasesRemoval()
        {
            Initialise();
            var program = GetProgram("Combinators.dfy");
            var daryController = GetDaryController(program);

            int count = daryController.Decreases.Count;
            foreach (var wildCardDecreasese in daryController.DecreasesWildCards) {
                count += wildCardDecreasese.Count;
            }
            Assert.AreEqual(5, count);
            Assert.AreEqual(1, daryController.FindRemovableDecreases().Count);
            Assert.True(daryController.IsProgramValid());

            int newCount = daryController.Decreases.Count;
            foreach (var wildCardDecreasese in daryController.DecreasesWildCards) {
                newCount += wildCardDecreasese.Count;
            }
            Assert.AreEqual(4, newCount);
        }

        [Test]
        public void LemmaCallRemoval()
        {
            Initialise();
            var program = GetProgram("Streams.dfy");
            var daryController = GetDaryController(program);

            Assert.AreEqual(21, daryController.LemmaCalls.Count);
            Assert.AreEqual(17, daryController.FindRemovableLemmaCalls().Count);
            Assert.AreEqual(4, daryController.LemmaCalls.Count);
            Assert.True(daryController.IsProgramValid());
        }

        [Test]
        public void SimplifyAsserts()
        {
            Initialise();
            var program = GetProgram("CombinedAsserts.dfy");
            var daryController = GetDaryController(program);

            var simplifiedAsserts = daryController.GetSimplifiedAsserts();
            Assert.AreEqual(1, simplifiedAsserts.Count);
            Assert.True(daryController.IsProgramValid());
            var assert = (AssertStmt) simplifiedAsserts[0].Item2;
            Assert.True(assert.Expr is ParensExpression);
            Assert.True(daryController.IsProgramValid());
            //TODO looking into the assertStmt to make sure it actually broke down
        }

        [Test]
        public void SimplifyInvariants()
        {
            Initialise();
            var program = GetProgram("ListCopy.dfy");
            var daryController = GetDaryController(program);

            var simplifiedInvariants = daryController.GetSimplifiedInvariants();
            Assert.AreEqual(1, simplifiedInvariants.Count);
            Assert.True(daryController.IsProgramValid());
        }

        [Test]
        public void TestCalcStatements()
        {
            Initialise();
            var program = GetProgram("Calc.dfy");
            var daryController = GetDaryController(program);

            var removedCalcs = daryController.FindRemovableCalcs();

            using (TextWriter tw = File.CreateText("H:\\dafny\\calc.dfy"))
            {
                daryController.PrintProgram(tw);
            }

            Assert.AreEqual(3, removedCalcs.Item1.Count);
            Assert.AreEqual(1, removedCalcs.Item2.Count);
            Assert.AreEqual(1, removedCalcs.Item4.Count);
            Assert.True(daryController.IsProgramValid());
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
            
            var daryController = GetDaryController(SimpleCloner.CloneProgram(program));
            var data = daryController.FastRemoveAllRemovables();
            Assert.AreEqual(1, data.SimplifiedInvariants.Count);
        }

        [Test]
        public void TestSimultaneousAllTypeRemoverCalcs() {
            Initialise();
            var program = GetProgram("Calc.dfy");
            var daryController = GetDaryController(program);

            var data = daryController.FastRemoveAllRemovables();
            var simplifiedCalcs = data.SimplifiedCalcs;
            var removedCalcs = data.RemovableCalcs;

            bool wayOne = simplifiedCalcs.Item1.Count == 3 && simplifiedCalcs.Item2.Count == 1;
            bool wayTwo = simplifiedCalcs.Item1.Count == 2 && simplifiedCalcs.Item2.Count == 2;

            Assert.True(wayOne || wayTwo);
            Assert.AreEqual(1, removedCalcs.Count);
            Assert.True(daryController.IsProgramValid());
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

            var oneAtATime = new DaryController(oneAtATimeProg, new OneAtATimeRemover(oneAtATimeProg));
            var simultaneous = new DaryController(simulProg, new SimultaneousMethodRemover(simulProg));
            var allType = new DaryController(SimpleCloner.CloneProgram(program));
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

            using (TextWriter tw = File.CreateText("H:\\dafny\\oaat.dfy")) {
//            using (TextWriter tw = File.CreateText("C:\\users\\Duncan\\Documents\\oaat.dfy")) {
                oneAtATime.PrintProgram(tw);
            }
            using (TextWriter tw = File.CreateText("H:\\dafny\\allType.dfy")) {
//            using (TextWriter tw = File.CreateText("C:\\users\\Duncan\\Documents\\simult.dfy")) {
                allType.PrintProgram(tw);
            }
            using (TextWriter tw = File.CreateText("H:\\dafny\\simul.dfy")) {
//            using (TextWriter tw = File.CreateText("C:\\users\\Duncan\\Documents\\allType.dfy")) {
                simultaneous.PrintProgram(tw);
            }


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
            var dary = new Dary.Dary(stop);
            var program = GetProgram("Calc.dfy");

            var results = dary.ProcessProgram(program);
        }
    }
}
