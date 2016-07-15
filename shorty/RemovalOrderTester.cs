using System.Collections.Generic;
using System.IO;
using Microsoft.Dafny;

namespace shorty
{
    internal class RemovalOrderTester<T>
    {
        private readonly Dictionary<MemberDecl, List<Wrap<T>>> _memberWrapDictionary;
        private readonly Program _program;
        private bool _allRemoved;

        public RemovalOrderTester(Dictionary<MemberDecl, List<Wrap<T>>> memberWrapDictionary, Program program)
        {
            _memberWrapDictionary = memberWrapDictionary;
            _program = program;
        }

        public Dictionary<Method, List<List<T>>> TestDifferentRemovals()
        {
            var returnData = new Dictionary<Method, List<List<T>>>();
            foreach (var memberDecl in _memberWrapDictionary.Keys) {
                if(_memberWrapDictionary[memberDecl].Count == 0) continue;
                _allRemoved = false;
                var method = memberDecl as Method;
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
                solutions.Add(currentSolution);
                //if all items were removed we want to stop now!
                if (solutions.Count == _memberWrapDictionary[method].Count)
                    _allRemoved = true;
                return;
            }
            var item = _memberWrapDictionary[method][index].Removable;
            var parent = _memberWrapDictionary[method][index].ParentList;
            TryRemovingItemForOrderingTest(item, parent, method, index, currentSolution, solutions);
        }

        private void TryRemovingItemForOrderingTest(T item, List<T> parent, Method method, int index, List<T> currentSolution, List<List<T>> solutions)
        {
            if (_allRemoved)
                return;
            var assertPos = parent.IndexOf(item);
            parent.Remove(item);
            var validator = new SimpleVerifier();
            if (validator.IsProgramValid(_program)) {
                var newCurrentSolution = new List<T>(currentSolution) {item}; //create a copy of the currentSolution and add in the item
                TestRemovalOrdering(index + 1, solutions, newCurrentSolution, method);
                if (_allRemoved) return;
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