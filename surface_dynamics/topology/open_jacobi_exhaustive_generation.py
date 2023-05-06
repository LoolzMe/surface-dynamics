import itertools
from .fat_graph import FatGraph, list_extrems
from .fat_graph_exhaustive_generation import FatGraphs
from surface_dynamics.misc.permutation import perm_cycles
import surface_dynamics.misc.linalg as linalg
from sage.rings.all import ZZ, QQ
from sage.matrix.constructor import matrix
from sage.modules.free_module_element import vector
import surface_dynamics.misc.multiproc as mp

from collections import deque


import json
# from sage.vector.constructor import vector

from itertools import filterfalse


### Legacy part

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


### Legacy part ends

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

def importGraphs(filename):
    in_file = open(filename, "r")
    dump = json.load(in_file)
    in_file.close()

    F = []
    for graph in dump:
        F.append(FatGraph(vp=graph['vp'], ep=graph['ep']))

    return F

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

def IHX_edges(graph, ti, ei, dir='l'):
    new_graph = graph.__copy__()

    # print(graph)
    # print(ti)
    # print(hi)
    # print(dir)
    new_graph.change_ihx_edge(ti, ei, dir)
    new_graph.relabel_fully(0)

    return new_graph



def isolateGraphStructure(graph, nc=None):
    """Generates graph structure without hairs, It's given in adjecent representation

    Args:
        graph (FatGraph): graph

    Returns:
        List: adjecent list, each object corresponds to each node
    """
    if nc == None:
        nc = graph._nv

    
    indexes = {} # dict for indexes coz we need relabel vertices
    aval_index = 0

    for i in range(nc):
        if graph.is_one_half(i):
            continue

        stable = graph.find_vertex_vi(i)
        pivot = graph.find_vertex_vi(i)

        if not i in indexes:
            indexes[i] = aval_index
            aval_index += 1

        while True:
            branch_i = graph._ep[pivot]
            branch_vi = graph._vl[branch_i]
            if not graph.is_one_half_dot(branch_i):
                if not branch_vi in indexes:
                    indexes[branch_vi] = aval_index
                    aval_index += 1

            pivot = graph._vp[pivot]

            if pivot == stable:
                break


    adj_graph = [set() for _ in range(len(indexes))]
    
    for i in range(nc):
        if graph.is_one_half(i):
            continue

        stable = graph.find_vertex_vi(i)
        pivot = graph.find_vertex_vi(i)


        while True:
            branch_i = graph._ep[pivot]
            branch_vi = graph._vl[branch_i]
            if not graph.is_one_half_dot(branch_i):
                adj_graph[indexes[branch_vi]].add(indexes[i])
                adj_graph[indexes[i]].add(indexes[branch_vi])

            pivot = graph._vp[pivot]

            if pivot == stable:
                break

    
    return [list(set_) for set_ in adj_graph]

def hamiltonian_path(adj_list, path, visited, index, vortex, paths, lock):

    #Base condition: if the vertex is the start vertex
    #and all nodes have been visited (start vertex twice)
    if vortex == 0 and index == len(adj_list):
        with lock:
            paths.append(path[:])
        # return to explore more cycles
        return

    #iterate through the neighbor vertices
    for vertex in adj_list[vortex]:
        if visited[vertex] == 0:
            nbr = vertex
            #visit and add vertex to the cycle
            visited[nbr] = 1
            path.append(nbr)

            #traverse the neighbor vertex to find the cycle
           
            hamiltonian_path(adj_list, path, visited, index+1, nbr, paths, lock)


        #Backtrack
            visited[nbr] = 0
            path.pop()

def findAllHamiltonianPaths(adj_list):
    # Use a multiprocessing lock to synchronize access to the paths list
    

    # Create a list to store the visited vertices
    visited = [False] * len(adj_list)

    with mp.get_Manager() as manager:
        # Call the backtracking function to find all Hamiltonian paths
        lock = manager.Lock()
        paths = manager.list()

        
        hamiltonian_path(adj_list, [0], visited, 0, 0, paths, lock)


        # Return the unique paths
        unique_paths = set(tuple(path) for path in list(paths))
        return list(itertools.islice(unique_paths, len(unique_paths) // 2))


class openJDLinearSpace(linalg.LinearSpace):
    
    def __init__(self, nv3, nh, bases=[], field=QQ) -> None:
        super().__init__(field, bases=bases)
        self._nv3 = nv3
        self._nh = nh
        self._nc = nv3 + nh
        self._nd = 3*nv3 + nh
        self._corr_dict = [{}] * self._nd
        self.DIR = {0: 'l', 1: 'r'}

        self.buildCorrDict()
        # self.reduceSpace()
        self._bases = self._space
        self._matrix = matrix(field, [field(0)]*len(self._bases))
        self._pmatrix = None
        self._pprojector = None
        self._phamiltonians = None

        # self.constructProjMatrix()

        # self.buildCorrDict()


    def buildCorrDict(self):
        for i, b in enumerate(self._space):
            self._corr_dict[0][b.to_string()] = i

        for r in range(1, self._nd):
            for i, b in enumerate(self._space):
                new_b = b.__copy__()
                new_b.relabel_fully(r)
                self._corr_dict[r][new_b.to_string()] = i

    # 
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
            

        self._space = [graph for i, graph in enumerate(self._space) if not i in exclude_ones]

        self.buildCorrDict()

    def reduceAS(self, base):
        b = base
        rows = []
        for i in range(self._nc):
            if b.is_one_half(i):
                continue

            d = AS(b, i)
            di = self.searchRecursive(d)

            if di == -1:
                continue
            
            rows.append(self.returnEquation([1, 1], [self.search(0, b), di], n=2))


        return rows

    def reductionAS_MP(self, cores=mp.get_cores()):
        with mp.get_Manager() as manager:
            with mp.MyPool(cores) as pool:
                results = pool.map(self.reduceAS, self._bases)
        

        matrix = self.createMatrix(results)
        self.stackMatrix(matrix)

        self.changeBasesFromMatrix()



    def reductionAS(self):
        results = []

        for base in self._bases:
            results.append(self.reduceAS(base))

        matrix = self.createMatrix(results)
        self.stackMatrix(matrix)

        self.changeBasesFromMatrix()

        # self.clearMatrix()


    def reduceIHX_edges(self, base):

        # using the fact that half-edges' inndexes from (0) to (nd - 1) 

        b = base
        rows = []

        for i in range(self._nd):
            if b.is_one_half_dot(i) or  b.is_one_half_dot(b._ep[i]) or b.is_next_hair(i) or not b.is_base_of_hair(i):
                continue

            for dir in range(2):
                
                if dir == 0 and b.is_next_one_half_dot(b._vp[b._vp[i]]):
                    continue
                if dir == 1 and b.is_next_one_half_dot(b._vp[i]):
                    continue

                d1 = IHX_edges(b, 0, i, self.DIR[dir])
                d2 = IHX_edges(b, 1, i, self.DIR[dir])

                di1 = self.searchRecursive(d1)
                di2 = self.searchRecursive(d2)

                if di1 == -1 or di2 == -1:
                    continue

                rows.append(self.returnEquation([1, -1, -1], [self.search(0, b), di1, di2], n=3))

        return rows

    def reduceIHX(self, base):
        b = base
        rows = []
        for i in range(self._nc):
            if b.is_one_half(i):
                continue

            pivot = b.find_vertex_vi(i)

            # print(b)

            # hair
            if b.is_base_of_hair(pivot):
                # print(b)
                pass
                # bei = b.find_hair_base_edge(pivot)
                
                # # print(pivot)
                # for dir in range(2):
                #     branch_ei = b._ep[b._vp[bei]]
                #     if dir == 0 and (b.is_base_of_hair(branch_ei) or b._vl[bei] == b._vl[branch_ei]):
                #             continue
                #     if dir == 1 and (b.is_base_of_hair(b._ep[b._vp[b._vp[bei]]]) or b._vl[bei] == b._vl[b._ep[b._vp[b._vp[bei]]]]):
                #         continue
                    
                #     d1 = IHX(b, 0, bei, self.DIR[dir])
                #     d2 = IHX(b, 1, bei, self.DIR[dir])

                #     di1 = self.searchRecursive(d1)
                #     di2 = self.searchRecursive(d2)

                #     if di1 == -1 or di2 == -1:
                #         continue
                    
                #     # delete at the deployment
                #     if di1 == self.search(0, b) or di2 == self.search(0, b):
                #         continue

                #     rows.append(self.returnEquation([1, -1, -1], [self.search(0, b), di1, di2], n=3))
            
            # chord
            else:
                for _ in range(3):
                    for dir in range(2):
                        branch_ei = b._ep[b._vp[pivot]]
                        branch_eir = b._ep[b._vp[b._vp[pivot]]]
                        if dir == 0 and (b.is_base_of_hair(branch_ei) or b._vl[pivot] == b._vl[branch_ei] or b.are_same_edge_nodes(pivot, b._vp[branch_ei]) or b.are_same_edge_nodes(pivot, b._vp[b._vp[branch_ei]])):
                            continue
                        if dir == 1 and (b.is_base_of_hair(branch_eir) or b._vl[pivot] == b._vl[branch_eir] or b.are_same_edge_nodes(pivot, b._vp[branch_eir]) or b.are_same_edge_nodes(pivot, b._vp[b._vp[branch_eir]])):
                            continue
                        
                        d1 = IHX(b, 0, pivot, self.DIR[dir])
                        d2 = IHX(b, 1, pivot, self.DIR[dir])

                        di1 = self.searchRecursive(d1)
                        di2 = self.searchRecursive(d2)

                        if di1 == -1 or di2 == -1:
                            continue
                            
                        # delete at the deployment
                        if di1 == self.search(0, b) or di2 == self.search(0, b):
                            continue
                        
                        # print(d1, di1)
                        # print(d2, di2)
                        rows.append(self.returnEquation([1, -1, -1], [self.search(0, b), di1, di2], n=3))

                pivot = b._vp[pivot]

        return rows


    def reductionIHX_MP(self, cores=mp.get_cores()):
        with mp.get_Manager() as manager:
            with mp.MyPool(cores) as pool:
                results = pool.map(self.reduceIHX_edges, self._bases)
                results.extend(pool.map(self.reduceIHX, self._bases))
        
        # for rows in results:
        #     for row in rows:
        #         self.addRow(row)

        matrix = self.createMatrix(results)
        self.stackMatrix(matrix)

        self.changeBasesFromMatrix()


    def reductionIHX_edges(self):
        results = [self._field(0)] * len(self._space)

        for base in self._bases:
            results.append(self.reduceIHX_edges(base))


        matrix = self.createMatrix(results)
        self.stackMatrix(matrix)

        self.changeBasesFromMatrix()


    def reductionIHX(self):
        results = [self._field(0)] * len(self._space)

        for base in self._bases:
            results.append(self.reduceIHX(base))


        matrix = self.createMatrix(results)
        self.stackMatrix(matrix)

        self.changeBasesFromMatrix()


    def reductionIHX_final(self):
        self.reductionIHX_edges()
        self.reductionIHX()
        
    
    def constructProjMatrix(self, cores=mp.get_cores() // 2):
        adj_diagrams = []

        for diagram in self._space:
            adj_diagrams.append(isolateGraphStructure(diagram))

        with mp.MyPool(cores) as pool:
            result = pool.map(findAllHamiltonianPaths, adj_diagrams)

        self._pprojector = matrix(self._field, len(self._space), len(self._space), lambda x, y : 1 if (x == y) and (len(result[x]) > 0) else 0)
        self._phamiltonians = result

    def perfectDiagramsMatrix(self):
        # should be called after constructProjMatrix
        # and factor space creation

        self._pmatrix = self._matrix * self._pprojector

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

    def createMatrix(self, rows):
        flat_list = [item for sublist in rows for item in sublist]

        return matrix(self._field, flat_list)

    def stackMatrix(self, matrix):
        self._matrix = self._matrix.stack(matrix)
    
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
    
    def returnEquation(self, values, indexes, n=None):
        if n == None:
            n = len(values)

        row = [self._field(0)] * len(self._space)
        for value, index in zip(values, indexes):
            row[index] += value
        
        return row

    def addRow(self, row):
        self._matrix = self._matrix.stack(vector(self._field, row))
        



class dynamicJDSpace(openJDLinearSpace):

    def __init__(self, nv3, nh, bases=[], field=QQ) -> None:
        super().__init__(nv3, nh, bases, field)
        # self.buildCorrDict()


    def fillSpaceIHX(self, seed, n_iter=2):
        queue = deque()
        queue.append(seed)
        for i in range(n_iter):
            new_seeds = []
            while bool(queue):
                graph = queue.popleft()


    def reduceIHX(self, base):
        b = base
        rows = []
        for i in range(self._nc):
            if b.is_one_half(i):
                continue

            pivot = b.find_vertex_vi(i)

            # print(b)

            # hair
            if b.is_base_of_hair(pivot):
                # print(b)

                bei = b.find_hair_base_edge(pivot)
                
                # print(pivot)
                for dir in range(2):
                    branch_ei = b._ep[b._vp[bei]]
                    if dir == 0 and (b.is_base_of_hair(branch_ei) or b._vl[bei] == b._vl[branch_ei]):
                            continue
                    if dir == 1 and (b.is_base_of_hair(b._ep[b._vp[b._vp[bei]]]) or b._vl[bei] == b._vl[b._ep[b._vp[b._vp[bei]]]]):
                        continue
                    
                    d1 = IHX(b, 0, bei, self.DIR[dir])
                    d2 = IHX(b, 1, bei, self.DIR[dir])

                    di1 = self.searchRecursive(d1)
                    di2 = self.searchRecursive(d2)

                    if di1 == -1:
                        pass
                    if di2 == -1:
                        pass
                        
                    
                    # delete at the deployment
                    # if di1 == self.search(0, b) or di2 == self.search(0, b):
                    #     continue

                    rows.append(self.returnEquation([1, -1, -1], [self.search(0, b), di1, di2], n=3))
            
            # chord
            else:
                for _ in range(3):
                    for dir in range(2):
                        branch_ei = b._ep[b._vp[pivot]]
                        if dir == 0 and (b.is_base_of_hair(branch_ei) or b._vl[pivot] == b._vl[branch_ei]):
                            continue
                        if dir == 1 and (b.is_base_of_hair(b._ep[b._vp[b._vp[pivot]]]) or b._vl[pivot] == b._vl[b._ep[b._vp[b._vp[pivot]]]]):
                            continue
                        
                        d1 = IHX(b, 0, pivot, self.DIR[dir])
                        d2 = IHX(b, 1, pivot, self.DIR[dir])

                        di1 = self.searchRecursive(d1)
                        di2 = self.searchRecursive(d2)

                        if di1 == -1 or di2 == -1:
                            continue
                            
                        # delete at the deployment
                        if di1 == self.search(0, b) or di2 == self.search(0, b):
                            continue

                        rows.append(self.returnEquation([1, -1, -1], [self.search(0, b), di1, di2], n=3))

                pivot = b._vp[pivot]

        return rows


    def addDiagram(self, diagram):
        id = len(self._space)
        self._space.append(diagram)
        
        
        return id



class openJDGenerator(object):

    def __init__(self, nv3, nh) -> None:
        """Initialization of the generator. We graduate linear space of JD on given args.

        Args:
            nv3 (int): number of 3-valent vertices
            nh (int): number of univalent vertices
        """

        # assert nv3 % 2 == 0

        self._nv3 = nv3 - nh

        assert self._nv3 % 2 == 0
        self._nh  = nh

        self._nv = 2*self._nh + self._nv3
        self._ne = 2*self._nh + 3 * self._nv3 // 2

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