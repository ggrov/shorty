using System.Collections.Generic;
using Microsoft.Dafny;

namespace shorty
{
    internal class RemovalOrderTester<T>
    {
        private readonly Dictionary<MemberDecl, List<Wrap<T>>> _memberWrapDictionary;
        private readonly Program _program;

        public RemovalOrderTester(Dictionary<MemberDecl, List<Wrap<T>>> memberWrapDictionary, Program program)
        {
            _memberWrapDictionary = memberWrapDictionary;
            _program = program;
        }

        public Dictionary<Method, List<List<T>>> TestDifferentRemovals()
        {
            var returnData = new Dictionary<Method, List<List<T>>>();
            foreach (var memberDecl in _memberWrapDictionary.Keys) {
                var method = (Method) memberDecl;
                if (method == null) continue;
                var solutions = new List<List<T>>();
                TestRemovalOrdering(0, solutions, new List<T>(), method);
                returnData.Add(method, solutions);
            }
            return returnData;
        }

        private void TestRemovalOrdering(int index, List<List<T>> solutions, List<T> currentSolution, Method method)
        {
            if (index == _memberWrapDictionary[method].Count) {
                solutions.Add(new List<T>(currentSolution));
                return;
            }
            var item = _memberWrapDictionary[method][index].Removable;
            var parent = _memberWrapDictionary[method][index].ParentList;
            TryRemovingItemForOrderingTest(item, parent, method, index, currentSolution, solutions);
        }

        private void TryRemovingItemForOrderingTest(T item, List<T> parent, Method method, int index, List<T> currentSolution, List<List<T>> solutions)
        {
            var assertPos = parent.IndexOf(item);
            parent.Remove(item);
            var validator = new SimpleVerifier();
            if (validator.IsProgramValid(_program)) {
                var newCurrentSolution = new List<T>(currentSolution) {item}; //create a copy of the currentSolution and add in the item
                TestRemovalOrdering(index + 1, solutions, newCurrentSolution, method);
                parent.Insert(assertPos, item);
                TestRemovalOrdering(index + 1, solutions, currentSolution, method);
            }
            else {
                parent.Insert(assertPos, item);
                TestRemovalOrdering(index + 1, solutions, currentSolution, method);
            }
        }
    }
}