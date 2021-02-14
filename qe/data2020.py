# https://eng-cs.syr.edu/wp-content/uploads/2020/09/CIS-exam-Jan-6-2020.pdf

import math

class Process:
    def __init__(self, name, rank, pid):
        self.name = name
        self.rank = rank
        self.pid = pid

    def __LE__(self, other):
        return self.rank <= other.rank
    

class BinaryHeap:
    def __init__(self):
        self._T = []

    def __getParent(self, n):
        '''
        get the parent index  of a node index at n
        '''
        parent = (n - 1) // 2
        return parent

    def __getChildren(self, n):
        '''
        get the children index of a node index at n
        '''
        l = n * 2 + 1
        r = n * 2 + 2
        if l >= len(self._T):
            l = None
        if r >= len(self._T):
            r = None
        return (l, r)
    
    def __heapfyParent(self, n):
        '''
        assume sub tree rooted at n is already a heap, make it's parent a heap
        '''
        if n == 0:
            return
        parentIndex = self.__getParent(n)
        if self._T[n] <= self._T[parentIndex]:
            self._T[n], self._T[parentIndex] = self._T[parentIndex], self._T[n]
        self.__heapfyParent(parentIndex)
    
    def insert(self, n):
        if self._T == []:
            self._T.append(n)
            return
        self._T.append(n)
        self.__heapfyParent(len(self._T) - 1)
    
    def find_min(self):
        return self._T[0]

    def __rm_min(self, n):
        cl, cr = self.__getChildren(n) 
        if cl is None:
            self._T[n] = self._T[-1]
            self.__heapfyParent(n)
            return
        if cr is None:
            self._T[n] = self._T[cl]
            self._T[cl] = self._T[-1]
            self.__heapfyParent(cl)
            return
        if self._T[cl] <= self._T[cr]:
            self._T[n] = self._T[cl]
            self.__rm_min(cl)
        else:
            self._T[n] = self._T[cr]
            self.__rm_min(cr)

    def remove_min(self):
        _min = self._T[0]
        self.__rm_min(0)
        self._T = self._T[:-1]
        return _min


# test
a = BinaryHeap()
a.insert(2)
a.insert(7)
a.insert(8)
a.insert(5)
a.insert(1)
a.insert(3)

print(a.remove_min())
print(a.remove_min())
print(a.remove_min())