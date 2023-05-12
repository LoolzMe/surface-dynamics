"""
This program was written jointly by Vasily Dolgushev, Yeahuay Wu and Matthew Wynne
And modified by Vladyslav Tysiachnyi
"""

from sympy import flatten
"""
this command "flattens" a nested list or tuple; for instance 
flatten([[2,1,-1],[1,0,1,(0,-1,0)],(0,0,1)]) return 
[2, 1, -1, 1, 0, 1, 0, -1, 0, 0, 0, 1] and 
flatten((11,5,(0,1,[2,3]),-1,3)) returns 
[11, 5, 0, 1, 2, 3, -1, 3]
"""

from sympy import Matrix, zeros
from sympy import shape

"""
This command converts a nested list into a matrix 
(i.e. an instance of the class sympy.matrices.dense.MutableDenseMatrix) 
for more details, 
please see https://docs.sympy.org/latest/tutorial/matrices.html
"""

from sympy import sympify
"""
this command allows us to work with rational numbers 
exactly (in some sense, we ask the computer: "please, do not 
convert to float"); for instance, executing a=2/3 and type(a) we 
get "float"; however, executing a=sympify(2)/3 and type(a) we get 
"sympy.core.numbers.Rational" 
"""

from random import choice

import surface_dynamics.misc.linalg as linalg
from sage.rings.all import ZZ, QQ
from sage.matrix.constructor import matrix
from sage.modules.free_module_element import vector
import surface_dynamics.misc.multiproc as mp

import time

"""
itertools has a collection of useful functions for efficient 
looping (outputs are typically iterators); please see  

https://docs.python.org/3/library/itertools.html

for more details 
"""

from itertools import chain
"""
for instance, chain([0,2,3],(1,2),[5,-2,1]) generates the sequence 
0,2,3,1,2,5,-2,1
"""


from itertools import permutations as perm
"""
for instance, perm((1,2,3)) or perm([1,2,3]) generates the sequence 
of tuples: (1, 2, 3), (1, 3, 2), (2, 1, 3), (2, 3, 1), (3, 1, 2), (3, 2, 1)
"""

from itertools import combinations as comb
"""
comb(L,r) generates combinations of length r of elements from L
(no repetitions).
"""

from itertools import combinations_with_replacement as combR
"""
for example, combR((1,2,3),2) generates (1,1), (1,2), (1,3), 
(2,2), (2,3), (3,3).
"""

"""
from operator import itemgetter

itemgetter is useful for sorting lists; I 
do not think that we use it.
"""

from pickle import dump, load

"""
How to use pickle:
Given a Python object obJecT, we can store it in the file FILE 
by doing this:
    
dump(obJecT,open('FILE','wb'))

To unpickle the obJecT back, we do this:
    
FO = open('FILE','rb'); obJecT = load(FO)

Another option is to use the function load_now.
It is important to use ' ' around the name of the file. 
"""
#Tested
def load_now(FILE):
    """
    load_now (unpickles) the object from the FILE 'FileName';
    one should not forget to use ' '
    """
    FO = open(FILE,'rb')
    return load(FO)

from math import factorial as fact

from math import log
"""
of course, there are many more useful commands in the library "math"
"""

"""
AUXILIARY FUNCTIONS
"""

CHARS = '0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ+-.'
CHARS_INV = {j:i for i,j in enumerate(CHARS)}

def uint_base64_str(n, l=None):
    r"""
    EXAMPLES::

        sage: from surface_dynamics.misc.permutation import uint_base64_str

        sage: uint_base64_str(15)
        'f'
        sage: uint_base64_str(15, 3)
        '00f'

        sage: uint_base64_str(-1)
        '.'
        sage: uint_base64_str(-1, 3)
        '...'
    """
    n = int(n)
    if n == -1:
        if l is None:
            return CHARS[64]
        else:
            return CHARS[64] * l
    elif n < -1:
        raise ValueError("invalid negative integer")
    s = ''
    while n:
        s = CHARS[n % 64] + s
        n //= 64
    if l is not None:
        if len(s) > l:
            raise ValueError
        else:
            s = CHARS[0] * (l - len(s)) + s
    return s

"""
To test that a list L is sorted, one can use 
this command: L == sorted(L)
This command does not change the list L. 
"""

#tested
def odd_fact(m):
    """
    returns the "odd" factorial of m 
    """
    if m <= 0:
        return 1
    else:
        return m * odd_fact(m-2)


#tested, we use it for testing.
def no_repeat(L,timed=None):
    """
    L is a list or a tuple. 
    no_repeat returns True if there are no repetitions in L.
    Otherwise, it returns False.
    """
    if timed:
        t0=time.time()
    for c in comb(L,2):
        if c[0] == c[1]:
            return False
    if timed:
        print('Time= ', time.time()-t0)
    return True

#tested, we use it for testing.
def no_repeat1(L,timed=None):
    """
    L is a list or a tuple. 
    no_repeat1 returns True if there are no repetitions in L.
    Otherwise, it returns False. COMMENT: I am surprised that this
    function works faster than no_repeat
    """
    if timed:
        t0=time.time()
    new = []; c=0
    for e in L:
        c=c+1
        if e not in new:
            new.append(e)
        if len(new)<c:
            return False
    if timed:
        print('Time= ', time.time()-t0)
    return len(new)==len(L)


"""
AUXILIARY FUNCTIONS END
"""

"""
We use two ways of representing a chord diagram
1) using lists of integers 1,2,...m in which each integer appears exactly two times; 
in this case we say that a chord diagram is represented by a sequence. 

Let t be a such a list and L be the corresponding list of elements of t 
WITHOUT repetitions and elements of L appear in the same order they appear in t.
We say that t is the standard form of the chord diagram (with m chords) if 
L = [1,2,3,...,m]. For example, [1,2,2,1] is the standard form of the 
(linear) chord diagram and [2,1,1,2] or [3,4,4,3] or [5,4,4,5] are examples of 
non-standdard forms of the same chord diagram  [1,2,2,1]. 
The function is_stand(t) below tests whether a list of 2m integers is in the 
standard form.
    
2) using graphs, (sorted) lists of edges. 
The lists [1,2,1,2], [2,1,2,1] and the nested list [(1,3),(2,4)] represent the same 
chord diagram with 2 chords; in this case, we say that a chord diagram is represented by 
a graph.  
"""

"""
An instance of Ch_diag is a (circular) chord diagram.
self.seq returns the sequence representation of the chord diagram
self.m returns the number of chords. 

"""
class Ch_diag:
    def __init__(self, seq):
        self.seq = seq
        self.m=len(seq)//2
    #tested
    def graph(self):
        """
        returns the graph representation of the chord diagram;
        for example,Ch_diag([2,3,1,1,2,3]).graph() returns [(1, 5), (2, 6), (3, 4)]
        """
        m = self.m; seq = self.seq
        out = []
        for i in range(1,m+1):
            out.append(tuple(id+1 for id, item in enumerate(seq) if item == i))
        return sorted(out)
    #tested
    def stand_seq(self):
        """
        c is an instance of a class Ch_diag;
        the function returns the representation of the corresponding
        chord diagram as the standard sequence. 
        For example, if c.seq is [2,1,2,1] then c.stand_seq() is [1,2,1,2].
        If c.seq is [1,3,2,3,2,1] then c.stand_seq() is [1, 2, 3, 2, 3, 1]
        """
        s = []
        for i in self.seq:
            if i not in s:
                s.append(i)
        return [s.index(j)+1 for j in self.seq]
    #tested
    def can_form(self):
        """
        returns the canonical representation of the circular chord diagram self
        (in the format of a sequence)
        """
        c = self.stand_seq(); d = len(c)
        t = self.stand_seq()
        for i in range(d-1):
            t = t[1:]+[t[0]] # we applied the cyclic permutation
            cc =Ch_diag(t).stand_seq() # we may need to bring it to the standard form
            if cc < c:
                c=cc
        return c

    def to_string(self):
        n = len(self.seq)
        l = int(log(n, 64)) + 1 # number of digits used for each entry
        std = self.can_form()
        return ''.join(uint_base64_str(std[i], l) for i in range(n))


class ChordsLinearSpace(linalg.LinearSpace):
    def __init__(self, bases, field=ZZ) -> None:
        super().__init__(bases)
        self._corr_dict = {}
        
        self._matrix = matrix(field, [field(0)]*len(self._bases), sparse=True)
        self._vec_matrix = None


        for i, chord in enumerate(bases):
            self._corr_dict[chord.to_string()] = i

    def reduceByRelation(self, relation_list):
        for relation in relation_list:
            coefs = []
            indexes = []
            for coef, chord in relation:
                coefs.append(coef)
                indexes.append(self.search(Ch_diag(chord)))
            
            self.addEquation(coefs, indexes)
        
        self.changeBasesFromMatrix()

    def ifBasis(self, diagrams):
        dim = len(self._matrix) - self._matrix.rank()

        indexes = []
        for diagram in diagrams:
            indexes.append(self.search(Ch_diag(diagram)))

        b_matrix = self._vec_matrix.matrix_from_rows(indexes)

        if b_matrix.rank() == dim:
            return True
        else:
            return False

    def fromDiagramsToColumn(self):
        i = 0
        j = 0
        e_i = len(self._matrix.columns())
        e_j = len(self._matrix.rows())
        echelon_matrix = self._matrix.echelon_form()
        self._vec_matrix = matrix.identity(self._field, len(self._space))

        k = 0
        while i != e_i and j != e_j:
            m = echelon_matrix[j, i]
            if m == self._field(1):
                echelon_matrix[j, i] = 0
                echelon_matrix.rescale_row(j, -1)
                self._vec_matrix[k] = echelon_matrix[j]
                i += 1
                j += 1
                k += 1
            else:
                # vector(self._field, [self._field(0)] * len(self._space))
                # vector[i] += 1
                # self._vec_matrix[k, i] += self._field(1)
                i += 1
                k += 1

    
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

    def search(self, chord):
        return self._corr_dict[chord.to_string()]


    def addEquation(self, values, indexes, n=None):
        if n == None:
            n = len(values)

        row = [0] * len(self._space)
        for value, index in zip(values, indexes):
            row[index] += value
        
        self.addRow(row)

    def addRow(self, row):
        self._matrix = self._matrix.row_insert(0, Matrix(row).T)

    def getCorrDict(self):
        return self._corr_dict        

    def clearMatrix(self):
        self._matrix = Matrix([0]*len(self._space))

    def getBasis(self):
        return self._bases

    def getMatrix(self):
        return self._matrix
    
    def getSpace(self):
        return self._space




# tested
def can_form_lc(v):
    """
    v is a linear combination of chord diagrams;
    the function returns the corresponding linear 
    combination of chord diagrams in the canonical form
    """
    return [(t[0],Ch_diag(t[1]).can_form()) for t in v]


"""
Examples of chord diagrams
"""

ch2 = [1,2,1,2]
ch3 = [1,2,3,1,2,3]
ch3_1= [2,3,1,1,2,3]

def is_stand(t):
    """
    t is a list of 2m integers in which integer appears exactly twice;
    the function returns True if t is the standard form of the corresponding
    linear chord diagram. Otherwise, it returns False.  
    """
    v = len(t)
    if v%2==1:
        print('Your input ', t,' does not presenent a chord diagram.')
        return None
    m = v//2; L = []
    for i in t:
        if i not in L:
            L.append(i)
    return L == [j for j in range(1,m+1)]



#tested
def graph2seq(t):
    """
    converts a chord diagram from the format of the graph (list of edges) 
    to the format of a sequence (list of positive integers)
    For example, [(1,3),(2,6),(4,5)] -->  [1,2,1,3,3,2].
    Note that, if the input is non-standard, the output is also non-standard.
    For example, [(2,6),(1,3),(4,5)] --> [2, 1, 2, 3, 3, 1].
    """
    r_list = [None]*(len(t)*2)
    for idx, entry in enumerate(t):
        r_list[entry[0]-1] = idx+1
        r_list[entry[1]-1] = idx+1
    return r_list


"""
This is a faster way to generate linear chord diagrams.
We generate chord diagrams in the format of a nested tuple.
Then we convert the result to the list like this one [1,2,1,3,2,3]. 
It corresponds to the chord diagram ((1,3), (2,5), (4,6)).  
"""
#tested
def ch_diag(m, timed=None):
    if timed:
        t0=time.time()
    def test01(tt):
        for el in tt:
            if el[0] > el[1]:
                return False
        return True
    t2m = [i for i in range(1,(2*m)+1)]
    for f in comb(t2m,m):
        L = [i for i in t2m if i not in f]
        for s in perm(L):
            t = tuple((f[i],s[i]) for i in range(m))
            if test01(t):
                yield(graph2seq(t))
    if timed:
        print('time in seconds=', time.time()-t0)

"""
This piece of code was used for testing ch_diag:

for m in range(1,7):
    L = list(ch_diag(m))
    print(fact_odd(m), len(L)==fact_odd(m), no_repeat(L))

"""

#tested
def circ_diag(m, timed=None):
    """
    returns the list of all (distinct) circular chord diagrams with m chords in the format 
    of list. BE CAREFUL! The function will work for a while for m > 7 ?
    VD: It uses a bit faster version of can_form, so it works a bit faster.
    """
    out = []
    if timed:
        t0=time.time()
    for c in ch_diag(m):
        cc = Ch_diag(c).can_form()
        if cc not in out:
            out.append(cc)
    if timed:
        print('time in seconds =', time.time()-t0)
    return out


"""
We need a function which splits a tuple into 4 subtuples. 
The order should be preseved. A subtuple can be empty.
"""
#tested
def part4(t):
    """
    generates all partitions of a tuple into 4 (possibly empty) subtuples
    """
    n = len(t)
    for i in combR(range(n+1),3):
        yield t[:i[0]], t[i[0]:i[1]],t[i[1]:i[2]], t[i[2]:]
        
#tested        
def generatePartitions(m):
    """
    for every chord diagram c with m-2 chords, 
    
    returns a list of generators, each generator in the list contains the partitions of one element of C_m
    for example, for m=4 
    """
    def add_two(diagram):
        return [el+2 for el in diagram]
    return [part4(add_two(element)) for element in ch_diag(m-2)]



"""
VD: NOOOOOOOO! the row is too long!!!
The number of circular chord diagrams is smaller!
"""

#tested
def makerow(l,s):
    """
    s is the size (length of the row).
    [(-1,3), (12,2), (-7,5)] with s = 5 goes to [0,12,-1,0,-7]
    """
    row = [0]*s
    for el in l:
        index = el[1]-1
        row[index] = el[0]
    return row


"""
To generate 4T relations for circular chord diagrams, we need this list:
"""
fourT1 = [((1,),(1,2),(2,),()), ((1,),(2,1),(2,),()),
          ((1,),(2,),(2,1),()), ((1,),(2,),(1,2),())]


"""
VD: I am trying to define a generator of all 4T relations
of circular chord diagrams.
Wel... does it give what we want?

This function works only for m>1. 
For m=2, it returns nothing and this is correct
"""
def gen_4T(m):
    coefs_4T = [1, -1, -1, 1]

    def h(tee,ptn):
        v = []
        for i in range(4):
            foo = flatten(zip(ptn, tee[i]))
            foo_c = Ch_diag(foo).can_form()
            v.append((coefs_4T[i], foo_c))
        return simplify(v)

    for part in generatePartitions(m):
        for ptn in part:
            rel=h(fourT1,ptn)
            if rel!=[]:
                yield rel


"""
OLD VERSIONS OF SOME FUNCTIONS.
WE MAY NEED THEM FOR TESTING...
"""


"""
'CircChUpTo8' is the storage file for the list of all chord 
circular chord diagrams up to m = 8 chords. 


old version for generating all 4-T relations for circular
diagrams; it depends on the storage file 'CircChUpTo8';
the output is a matrix represented as a nested list
"""
def gen_4T_old(m):
    mat = []
    coefs_blah = [1, -1, -1, 1]
    CD = load('CircChUpTo8') # loading circular chord diagrams
    size = len(CD[m-1])

    def h(tee,ptn):
        v = []
        for i in range(4):
            coef = coefs_blah[i]
            foo = flatten(zip(ptn, tee[i]))
            foo_c = can_form_b(foo)
            idx = CD[m-1].index(foo_c)
            v.append((coef, idx))
        return simplify(v)

    def g_1(ptn):
        rv0 = h(fourT1,ptn)
        return makerow(rv0,size)

    for part in generatePartitions(m):
        for ptn in part:
            mat.append(g_1(ptn))

    return mat


    
"""
Permutations in S_{0,1,..,n-1} are represented as tuples (i_0,...,i_{n-1}). 
0 --> i_1, 1--> i_1, ... n-1 --> i_{n-1}.
VD: This is not great! Do we start counting with 1 or with 0?...
"""
#tested
def inv(s):
    """
    returns the inverse of the permutation s
    """
    n = len(s)
    return tuple(s.index(i) for i in range(n))

#tested
def mt(m):
    """
    mt(m) is the tuple (1,2,..., m,1,2,..,m)
    """
    t = tuple(i for i in range(1, m+1))
    return t+t

#tested
def shuffle2(s):
    """
    s is a permutation of (1,2,...,2m)
    shuffle2 returns True is for every i \in {0,1,...,m-1}
    s[i]<s[i+m]. Otherwise, it returns False.
    """
    m = len(s)//2
    for i in range(m):
        if s[i] > s[i+m]:
            return False
    return True

#tested
def shuffle_m(s):
    """
    s is a permutation of (1,2,...,2m)
    shuffle2 returns True is for every i,j \in {0,1,...,m-1}
    i < j => s[i]< s[j] Otherwise, it returns False.
    """
    m = len(s)//2
    for i in range(m-1):
        if s[i]>s[i+1]:
            return False
    return True

"""
Good news! The number of diagrams with m chords coincides with
(2m-1)!! There should be a faster way to generate chord diagrams. 
Please, see https://oeis.org/A001147
"""
#tested
def chords(m): 
    """
    generates all chord diagrams with m chords
    """
    tm = mt(m)
    for s in perm(range(2*m)):
        if shuffle2(s) and shuffle_m(s):
            s1 = inv(s)
            yield tuple(tm[s1[i]] for i in range(2*m))




#tested
def ch2stand(c):
    """
    this is the old way to find a standard form of a chord diagram
    c is in the format of the sequence. 
    For example, ch2stand([2,1,2,1]) returns [1,2,1,2]. 
    In the above version, we use the class Ch_diag
    """
    s = ()
    for i in c:
        if i not in s:
            s = s + (i,)
    return [s.index(j)+1 for j in c]



#tested
def orbit(t):
    """
    returns the orbit of the chord diagram with respect to the
    action of the cyclic group; the input should be in the format of list
    """
    t = ch2stand(t) # what if the input is non-standard?
    out = [t]
    for i in range(len(t)-1):
        t = t[1:]+[t[0]] # we applied the cyclic permutation
        #print(t) # used for testing
        tt =ch2stand(t) # we may need to bring it to the standard form
        if tt not in out:
            out.append(tt[:])
    return out

"""
Another (slower) way to find the canonical form of a chord diagram 
is to use the command min(orbit)
"""

    
#tested
def can_form_old(t):
    """
    returns the canonical form of the circular chord diagram given 
    in the format of the sequence
    """
    c = ch2stand(t)
    for i in range(len(t)-1):
        t = t[1:]+[t[0]] # we applied the cyclic permutation
        #print(c) # used for testing
        cc =ch2stand(t) # we may need to bring it to the standard form
        if cc < c:
            c=cc
    return c



#tested
def circ_diag_old(m, timed):
    """
    returns the list of all (distinct) circular chord diagrams with m chords in the format 
    of list. BE CAREFUL! The function will work for a while for m > 7 ?
    """
    out = []
    if timed==True:
        t0=time.time()
    for c in ch_diag(m):
        cc = can_form_old(c)
        if cc not in out:
            out.append(cc)
    if timed==True:
        print('Elapsed time =', time.time()-t0)
    return out




"""
THE CODE BELOW IS NOT USED...
"""     


#tested
def ch_test(t):
    """
    t is a tuple of numbers 1,2,...,m; each number appears exactly once.
    ch_test(t) returns True if t is an admissible tuple: if i< j then 
    the first appearance of i should preceed the first appearance of j.
    """
    j =0
    for i in t:
        if i > j:
            if i == j+1:
                j = i
            else:
                return False
    return True

        

