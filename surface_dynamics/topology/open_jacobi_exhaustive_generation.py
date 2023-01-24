from .fat_graph import FatGraph, list_extrems
from .fat_graph_exhaustive_generation import FatGraphs
from surface_dynamics.misc.permutation import perm_cycles
import surface_dynamics.misc.linalg as linalg
from sage.rings.all import ZZ, QQ
from sage.matrix.constructor import matrix
from sage.modules.free_module_element import vector

import json
# from sage.vector.constructor import vector

from itertools import filterfalse

# def filterJacobiGraph(graph):
    
#     cycles = graph.vertices()
#     for cycle in cycles:
#         if len(cycle) == 2 or len(cycle) < 1 or len(cycle) > 3:
#             return True
    
#     return False


# def filterJacobiGraphs(graphs):
#     new_graphs = list(filterfalse(filterJacobiGraph, graphs))
#     return new_graphs

def eqAutomorphism(aut1, aut2):
    return False

def printAllAut(cm):
    n = cm.num_darts()
    
    for i in range(n):
        check, aut = cm._is_canonical(i)
        if check:
            print(i, aut)

def saveGraphs(graphs, filename):
    if type(graphs) != list:
        graphs = [graphs]

    dumps = []
    for graph in graphs:
        dump = {}
        dump['vp'] = graph._vp
        dump['vl'] = graph._vl
        dump['ep'] = graph._ep
        dump['nv'] = graph._nv

        dumps.append(dump)
    
    out_file = open(filename, "w")
  
    json.dump(dumps, out_file)
  
    out_file.close()

def AS(graph, vi):
    """Generate opposite half-edge order on the vertex with index

    Args:
        graph (FatGraph): graph
        vi (int): index of vertex
    """
    new_graph = graph.__copy__()
    
    new_graph.invert_vertex_p(vi)
    new_graph.relabel_fully(0)

    return new_graph


def IHX(graph, ti, hi, dir='l'):
    

    new_graph = graph.__copy__()

    # print(graph)
    # print(ti)
    # print(hi)
    # print(dir)
    new_graph.change_ihx(ti, hi, dir)
    new_graph.relabel_fully(0)

    return new_graph


class openJDLinearSpace(linalg.LinearSpace):
    
    def __init__(self, nv3, nh, bases=[], field=QQ) -> None:
        super().__init__(field, bases=bases)
        self._nv3 = nv3
        self._nh = nh
        self._nc = nv3 + 2*nh
        self._nd = 3*nv3 + 4*nh
        self._corr_dict = [{}] * self._nd
        self.DIR = {0: 'l', 1: 'r'}

        self.buildCorrDict()
        self.reduceSpace()
        self._bases = self._space
        self._matrix = matrix(field, [field(0)]*len(self._bases))
        # self.buildCorrDict()


    def buildCorrDict(self):
        for i, b in enumerate(self._space):
            self._corr_dict[0][b.to_string()] = i

        for r in range(1, self._nd):
            for i, b in enumerate(self._space):
                new_b = b.__copy__()
                new_b.relabel_fully(r)
                self._corr_dict[r][new_b.to_string()] = i


    def reduceSpace(self):
        """Reduce space from identical graphs in the space
        """

        exclude_ones = {}
        # reduced_dict = [{}] * self._nd

        for i, graph in enumerate(self._space):
            for r in range(1, self._nd):
                s = self.search(r, graph)
                if s != -1 and s != i and not i in exclude_ones:
                    exclude_ones[s] = 1
                    break
            
            # if is_continue:
            #     continue

        self._space = [graph for i, graph in enumerate(self._space) if not i in exclude_ones]

        self.buildCorrDict()


    def reductionAS(self):
        for b in self._bases:
            for i in range(self._nc):
                if b.is_one_half(i):
                    continue

                d = AS(b, i)
                di = self.searchRecursive(d)

                # assert di != -1
                if di == -1:
                    continue
                
                self.addEquation([1, 1], [self.search(0, b), di], n=2)

                # row = [self._field(0)] * len(self._bases)
                # row[self.search(0, b)] += self._field(1)
                # row[di] += self._field(1)
                # self.addRow(row)

        self.changeBasesFromMatrix()
        # self.clearMatrix()

    def reductionIHX(self):
        for b in self._bases:
            for i in range(self._nc):
                if b.is_one_half(i):
                    continue

                pivot = b.find_vertex_vi(i)

                if b.is_base_of_hair(pivot):
                    # print(b)

                    bei = b.find_hair_base_edge(pivot)
                    
                    # print(pivot)
                    for dir in range(2):
                        branch_ei = b._ep[b._vp[bei]]
                        if dir == 0 and b.is_base_of_hair(branch_ei):
                                continue
                        if dir == 1 and b.is_base_of_hair(b._ep[b._vp[b._ep[branch_ei]]]):
                            continue
                        
                        d1 = IHX(b, 0, bei, self.DIR[dir])
                        d2 = IHX(b, 1, bei, self.DIR[dir])

                        di1 = self.searchRecursive(d1)
                        di2 = self.searchRecursive(d2)

                        if di1 == -1 or di2 == -1:
                            continue

                        self.addEquation([1, -1, -1], [self.search(0, b), di1, di2], n=3)
                
                else:
                    for _ in range(3):
                        for dir in range(2):
                            branch_ei = b._ep[b._vp[pivot]]
                            if dir == 0 and b.is_base_of_hair(branch_ei):
                                continue
                            if dir == 1 and b.is_base_of_hair(b._ep[b._vp[b._ep[branch_ei]]]):
                                continue
                            
                            d1 = IHX(b, 0, pivot, self.DIR[dir])
                            d2 = IHX(b, 1, pivot, self.DIR[dir])

                            di1 = self.searchRecursive(d1)
                            di2 = self.searchRecursive(d2)

                            if di1 == -1 or di2 == -1:
                                continue

                            self.addEquation([1, -1, -1], [self.search(0, b), di1, di2], n=3)

                    pivot = b._vp[pivot]

        self.changeBasesFromMatrix()

        
    def changeBasesFromMatrix(self):
        i = 0
        j = 0
        e_i = len(self._matrix.columns())
        e_j = len(self._matrix.rows())
        echelon_matrix = self._matrix.echelon_form()
        new_bases = []

        while i != e_i and j != e_j:

            m = echelon_matrix[j, i]
            if m == self._field(1):
                j += 1
                i += 1
            else:
                new_bases.append(self._space[i])
                i += 1

        self._bases = new_bases

    def searchRecursive(self, graph):
        di = -1
        r = 0

        while di == -1:
            if r == self._nd:
                break
                            
            di = self.search(r, graph)
            r += 1
        
        return di


    def clearMatrix(self):
        self._matrix = matrix(self._field, [self._field(0)]*len(self._space))

    def getBasis(self):
        return self._bases

    def getMatrix(self):
        return self._matrix
    
    def getSpace(self):
        return self._space

    def search(self, r,  graph):
        vps = graph.to_string()
        if vps in self._corr_dict[r]:
            return self._corr_dict[r][vps] 
        
        return -1

    def addEquation(self, values, indexes, n=None):
        if n == None:
            n = len(values)

        row = [self._field(0)] * len(self._space)
        for value, index in zip(values, indexes):
            row[index] += value
        
        self.addRow(row)

    def addRow(self, row):
        self._matrix = self._matrix.stack(vector(self._field, row))
        



class openJDGenerator(object):

    def __init__(self, nv3, nh) -> None:
        """Initialization of the generator. We graduate linear space of JD on given args.

        Args:
            nv3 (int): number of 3-valent vertices
            nh (int): number of hairs
        """

        assert nv3 % 2 == 0

        self._nv3 = nv3
        self._nh  = nh

        self._nv = 2*nh + nv3
        self._ne = 2*nh + 3 * nv3 // 2

        self._g_max = -((-(self._ne - self._nv + 1)) // 2) 

        self._Fs = []

        import time

        start = time.time()

        # print(self._nv, self._ne, self._g_max)
        self._Fs = FatGraphs(g_min=0, g_max=self._g_max + 1, nv=self._nv, ne=self._ne, vertex_min_degree=1, vertex_max_degree=3, vertex_degree_exclude_list=[2]).list()

        mid = time.time()

        print("generation: ", mid - start)

        self.filter()
        self.normalize()

        print("filtration: ", time.time() - mid)

    def getGraphs(self):
        return self._Fs
    
    
    def filter(self):
        self._Fs = list(filterfalse(self._filterSingle, self._Fs))

    def normalize(self):
        for f in self._Fs:
            f.relabel_fully(0)

    def _filterSingle(self, graph):
        return not graph.is_Jacobi()


def normalizeStatic(graphs):
    for f in graphs:
        f.relabel_fully(0)

    return graphs

def filterStatic(graphs):
    new_graphs = list(filterfalse(filterSingleStatic, graphs))
    return new_graphs

def filterSingleStatic(graph):
    return not graph.is_Jacobi()