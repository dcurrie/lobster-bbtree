

import testing
// import std
import bbtree


def isOrdered(root, minn:string) -> bool:
    var last = minn
    // foldl is inorder
    let folder = def(k,v): if last == minn or cmp(last, k) < 0: last = k; true else: false
    return foldl(root, true, folder)

def isOrderedR(root, maxx:string) -> bool:
    var last = maxx
    // foldr is revorder
    let folder = def(k,v): if last == maxx or cmp(last, k) > 0: last = k; true else: false
    return foldr(root, true, folder)

def returner():
    return 1, 2, 3

def forwarder():
    return returner()

def return3o2(x):
    if x == 0:
        return 1, 2, 3
    else:
        return 9, 8, 7

// ok...
def return3oe(x):
    if x <= 0:
        return 1, 2, 3
    else:
        return return3oe(x-1)
// fails to compile...
//def return3oe(x):
//    if x > 0:
//        return return3oe(x-1)
//    else:
//        return 1, 2, 3

run_test("hello world"):
    let tre0 = nil::BBTree<string,int>
    let tre1 = add(tre0, "hello", 1) // instantiate a BBTree with ("hello",1)
    let tre2 = add(tre1, "world", 2) // add ("world",2)
    //print tre2 //ok

    let res = []
    map(tre2, def(k,v): push(res, k); true)
    foldr(tre2, false, def(k,v): push(res, k); true)
    assert (concat_string(res," ") == "hello world world hello")

    assert isOrdered(tre2, "")
    assert isOrderedR(tre2, "")

    assert get(tre2, "hello", -1) == 1
    assert get(tre2, "world", -1) == 2
    assert get(tre2, "frobb", -1) == -1

    //ng
    //let tre3 = del(tre2, "hello")
    //assert get(tre3, "hello", -1) == -1

run_test("getNth"):
    var a, b, c = forwarder()
    assert(a == 1 and b == 2 and c == 3)

    a, b, c = return3o2(0)
    assert(a == 1 and b == 2 and c == 3)
    a, b, c = return3o2(1)
    assert(a == 9 and b == 8 and c == 7)
    a, b, c = return3oe(1)
    assert(a == 1 and b == 2 and c == 3)

    let tre0 = nil::BBTree<string,int>
    let tre1 = tre0.add("hello", 1) // instantiate a BBTree with ("hello",1)
    let tre2 = tre1.add("world", 2) // add ("world",2)

    var k, v = getNth(tre2, -1, "", 0)
    assert(k == "world" and v == 2)
    k, v = getNth(tre2, -2, "", 0)
    assert(k == "hello" and v == 1)
    k, v = getNth(tre2, -3, "", 0)
    assert(k == "" and v == 0)

    k, v = tre2.getNth(0, "", 0)
    assert(k == "hello" and v == 1)
    k, v = tre2.getNth(1, "", 0)
    assert(k == "world" and v == 2)
    k, v = tre2.getNth(2, "", 0)
    assert(k == "" and v == 0)


run_test("string sets"):
    var aa = nil::BBTree<string,bool>
    //number_to_string(number:int, base:int, minchars:int) -> string
    for(99) i: aa = aa.add(number_to_string(i+1, 10, 5), true)
    var bb = nil::BBTree<string,bool>
    for(99) i: bb = bb.add(number_to_string(i+33, 10, 5), true)
    let cc = intersection(aa, bb)
    assert(len(cc) == 67)
    assert(len(difference(cc, aa)) == 0)
    assert(len(difference(cc, bb)) == 0)
    assert(len(union(aa, bb)) == 131)
    assert(len(union(bb, aa)) == 131)
    //print len(difference(aa, bb))
    //print fold(difference(aa, bb)), proc (k: int, v: bool, b: string): string = discard v; $k & ";" & b, "")
    assert(len(difference(aa, bb)) == 32)
    assert(len(difference(bb, aa)) == 32)
    assert(len(symmetricDifference(aa, bb)) == 64)
    assert(len(symmetricDifference(bb, aa)) == 64)
    assert(setEqual(symmetricDifference(bb, aa), symmetricDifference(aa, bb)))
    assert(setEqual(union(bb, aa), union(aa, bb)))
    assert(setEqual(intersection(bb, aa), intersection(aa, bb)))
    assert(disjoint(intersection(bb, aa), symmetricDifference(aa, bb)))
    let numbers = toSet<string,bool>(["1", "2", "3", "4", "5"])
    assert(numbers.contains("2"))
    assert(numbers.contains("4"))


// random stress test of bbtree.nim

let STRESS_TEST_N =  2000
let BB_ITERATIONS =  4000 // 10000 ok
let MAXINT = 9223372036854775807
let MARKER = (-MAXINT) - 1

let chs = "0123456789_/abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"

assert 64 == chs.length

var tree:BBTree<string,int>? = nil

// vector_reserve(typeid:typeid, len:int) -> [any]

var qintree = 0
var q_ins = 0
var q_del = 0
// ng let intree = vector_reserve(typeof qintree, STRESS_TEST_N)
let intree = vector_reserve(typeof return, STRESS_TEST_N)

// xorshift64*
let xorshift64star_state = [97531, 987654321] /* The state must be seeded with a nonzero value. */

// i is the index of the random state so we can have multiple independent streams
//
def xorshift64star_next(i:int):
    var x = xorshift64star_state[i]
    x = x ^ (x >> 12) // a
    x = x ^ (x << 25) // b
    x = x ^ (x >> 27) // c
    xorshift64star_state[i] = x
    return x * 2685821657736338717

def xorshift64star_rand(i: int, n: int):
    let x = xorshift64star_next(i)
    return abs(x) % n

def init_random_tree():
    for (STRESS_TEST_N):
        intree.push(MARKER)
    qintree = 0
    q_ins = 0
    q_del = 0

def make_random_key_val(k: int) -> string, int:
    assert(k > 0)
    //xorshift64star_state[0] = k
    //let size = xorshift64star_rand(0, 16) + 8
    //let svec = vector_reserve(typeof return, size)
    //for(size):
    //    let idx = xorshift64star_rand(0, 64)
    //    svec.push(chs.substring(idx, 1))
    //return svec.concat_string(""), -k
    return number_to_string(k,36,1), -k

def tstput(k: int):
    let key, val = make_random_key_val(k)
    tree = tree.add(key, val)

def tstget(k: int) -> int:
    let key, val = make_random_key_val(k)
    //discard val
    return tree.get(key, 1)

def tstrem(k: int):
    let key, val = make_random_key_val(k)
    //discard val
    tree = tree.del(key)

def do_random_tree_op():
    let x = xorshift64star_rand(1, STRESS_TEST_N)
    let n = intree[x]
    if n == MARKER:
        // insert
        let k = 1 + xorshift64star_rand(1, MAXINT-1)
        //print("x " + x + " k " + k)
        tstput(k)
        intree[x] = k
        qintree += 1
        q_ins += 1
    else:
        // delete
        tstrem(n)
        intree[x] = MARKER
        qintree -= 1
        q_del += 1

def find_and_wipe_duplicate() -> int:
    for(STRESS_TEST_N) i:
        let n = intree[i]
        if n != MARKER:
            // in std: for_range(i + 1, STRESS_TEST_N) j:
            var j = i + 1
            while j < STRESS_TEST_N:
                if n == intree[j]:
                    // duplicate
                    intree[j] = MARKER
                    qintree -= 1
                    q_ins -= 1
                    return j // > 0
                j += 1
    return 0

def innerlp() -> int:
    //print(tree)
    for(STRESS_TEST_N) j:
        let n = intree[j]
        if n != MARKER:
            let v = tstget(n)
            assert(v <= 0)
            assert(v == -n)
            if v == 1:
                return true // break
    return false

let trees = []
let sizes = []

def outerlp():
    var stop = false
    // do():
    for(BB_ITERATIONS) i:
        if stop: return true
        do_random_tree_op()
        if innerlp(): return true
        //if innerlp(): return true from do
        let sz = tree.len
        if sz != q_ins - q_del:
            let dup = find_and_wipe_duplicate()
            if dup != 0:
                // whew!
                print "dup!"
        assert(sz == (q_ins - q_del))
        if stop or (sz != (q_ins - q_del)):
            //fprintf(stderr, "random err: %u nodes, %ld final size\n", sz, q_ins - q_del);
            assert(not stop)
            stop = true
        if ((i+1) % 1024) == 0:
            //write(stderr, ".")
            assert(isOrdered(tree, ""))
            assert(isBalanced(tree))
            trees.push(tree)
            sizes.push(tree.len)

def for2(xs, ys, fun): return for xs.length: fun(xs[_], ys[_])

def persistent_p():
    assert(trees.length == sizes.length)
    assert(trees.length > 0)
//    for(trees.length) i:
//        assert(isOrdered(trees[i], ""))
//        assert(isBalanced(trees[i]))
//        assert(trees[i].len == sizes[i])
//        assert(trees[i].len == trees[i].countKeys)
    for2(trees, sizes) (t, s):
        assert(isOrdered(t, ""))
        assert(isBalanced(t))
        assert(t.len == s)
        assert(t.len == t.countKeys)
    print("Checked " + trees.length + " trees for peristance")

run_test("timed random tree iterations"):
    let start = seconds_elapsed()
    //write(stderr, "        ")
    init_random_tree()
    outerlp()
    let finish = seconds_elapsed()
    persistent_p()
    print("")
    print("        CPU time " + (finish - start)
          + " s for " + BB_ITERATIONS + " loops, averaging "
          + ((finish - start) / BB_ITERATIONS) + " s per loop")
    print("        random q: " + q_ins + " inserts, " + q_del + " deletes, "
          + qintree + " qintree, " + (q_ins - q_del) + " final size")

// number_to_string(number:int, base:int, minchars:int) -> string

/*
import unittest, random, strutils, times
import bbtree




suite "test int,int bbtree.nim":

    # echo "suite setup"

    var root : BBTree[int,int] = nil
    let null = root

    var rand0 : Rand = initRand(0x987654321)

    setup:
        # echo "run before each test"
        discard

    teardown:
        # echo "run after each test"
        discard

    test "empty tree is ordered, balanced, has length zero":
        # give up and stop if this fails
        require(isOrdered(root, low(int)))
        check(isBalanced(root))
        check(len(root) == 0)

    test "one entry tree is ordered, balanced, has length one":
        root = add(root, 1, -1)
        check(isOrdered(root, low(int)))
        check(isBalanced(root))
        check(len(root) == 1)

    test "one entry tree lookup works":
        var res = get(root, 1, -42)
        check(res == -1)
        res = get(root, 3, -42)
        check(res == -42)
        check(isOrdered(root, low(int)))
        check(isBalanced(root))
        check(len(root) == 1)

    test "add items in increasing key order, check ordered, balanced, has length 21":
        for i in 2..<22:
            root = add(root, i, -i)
        check(isOrdered(root, low(int)))
        check(isBalanced(root))
        check(len(root) == 21)

    test "add items in decreasing key order, check ordered, balanced, has length 44":
        for i in (-44)..(-22):
            root = add(root, -i, i)
        check(isOrdered(root, low(int)))
        check(isBalanced(root))
        check(len(root) == 44)

    test "check that some items are in the length 44 tree":
        let (mk,mv) = getMin(root,(-99,99))
        check(mk == 1 and mv == -1)
        let (xk,xv) = getMax(root,(-99,99))
        check(xk == 44 and xv == -44)
        let av = get(root, 25, 500)
        check(av == -25)
        let (nk,nv) = getNth(root,6,(-99,99)) # nth is 0-based
        check(nk == 7 and nv == -7)
        let (pk,pv) = getNth(root,-7,(-99,99)) # -1 is last
        check(pk == 38 and pv == -38)
        let (k0,v0) = getMin(null,(-99,99))
        check(k0 == -99 and v0 == 99)
        let (k1,v1) = getMax(null,(-99,99))
        check(k1 == -99 and v1 == 99)
        check(isOrdered(root, low(int)))
        check(isBalanced(root))
        check(len(root) == 44)
        let (ek,ev) = getNth(root,98,(-99,99)) # off the end
        check(ek == -99 and ev == 99)
        let (bk,bv) = getNth(root,-77,(-88,88)) # off the end
        check(bk == -88 and bv == 88)

    test "check succ and pred functions in the length 44 tree":
        let (k1,v1) = getNext(root,3,(-99,99))
        check(k1 == 4 and v1 == -4)
        let (k2,v2) = getPrev(root,22,(-99,99))
        check(k2 == 21 and v2 == -21)
        let (k3,v3) = getPrev(root,1,(-99,99))
        check(k3 == -99 and v3 == 99)
        let (k4,v4) = getNext(root,low(int),(-99,99))
        check(k4 == 1 and v4 == -1)
        let (k5,v5) = getPrev(root,100,(-99,99))
        check(k5 == 44 and v5 == -44)
        check(isOrdered(root, low(int)))
        check(isBalanced(root))
        check(len(root) == 44)
        check(countKeys(root) == 44)
        check(rank(root,1,-99) == 0)
        for i in 2..44:
            check(rank(root,i,-99) == i-1)
        # for code coverage...
        for i in 2..45:
            let (k,v) = getPrev(root,i,(-99,99))
            check(k == i-1 and v == -(i-1))
        for i in 0..43:
            let (k,v) = getNext(root,i,(-99,99))
            check(k == i+1 and v == -(i+1))

    test "delete some items, check, check ordered, balanced, and length":
        root = del(root, 13)
        check(isOrdered(root, low(int)))
        check(isBalanced(root))
        check(len(root) == 43)
        var res = get(root, 13, -999)
        check(res == -999)
        res = get(root, 26, -999)
        check(res == -26)
        root = del(root, 26)
        check(isOrdered(root, low(int)))
        check(isBalanced(root))
        check(len(root) == 42)
        res = get(root, 26, -999)
        check(res == -999)
        res = get(root, 1, -999)
        check(res == -1)
        root = delMin(root)
        check(isOrdered(root, low(int)))
        check(isBalanced(root))
        check(len(root) == 41)
        res = get(root, 1, -999)
        check(res == -999)
        res = get(root, 44, -999)
        check(res == -44)
        root = delMax(root)
        check(isOrdered(root, low(int)))
        check(isBalanced(root))
        check(len(root) == 40)
        res = get(root, 44, -999)
        check(res == -999)
        check(delMin(null).isNil)
        check(delMax(null).isNil)
        check(del(null, 19).isNil)

    test "delete random items, check, check ordered, balanced, and length":
        var n = len(root)
        while n > 0:
            let i = rand(rand0, n-1)
            let (k0,v0) = getNth(root,i,(-99,99))
            discard v0
            check(k0 != -99)
            root = del(root, k0)
            let v1 = get(root,k0,99)
            check(v1 == 99)
            n = n-1
            check(len(root) == n)
            check(isOrdered(root, low(int)))
            check(isBalanced(root))

    test "using add to replace values":
        for i in 1..9:
            root = add(root, i, -i)
        check(isOrdered(root, low(int)))
        check(isBalanced(root))
        check(len(root) == 9)
        check(get(root,3,99) == -3)
        root = add(root, 3, -33)
        check(len(root) == 9)
        check(get(root,3,99) == -33)

suite "test opacity bbtree.nim":

    var root : BBTree[int,string] = nil

    root = add(root, 1, "one")

    test "opacity":
        # manually checked, generate compile errors as expected...
        # check(root.left == false)
        # check(root.right == false)
        # check(root.size == false)
        # check(root.key == false)
        # check(root.val == false)
        discard


suite "test map and fold bbtree.nim":

    var root : BBTree[int,int] = nil
    #let null = root

    for i in 1..<20:
        root = add(root, i, -i)

    test "fold to string":
        var d = fold(root,
                    proc (k: int, v: int, b: string): string = discard k; $v & ";" & b,
                    "")
        # echo d
        let s = split(d, {';'})
        var i = 0
        for k,v in inorder(root):
            check($v == s[i])
            i += 1
            discard k

    test "map to string":
        let t2 = map(root,
                    proc (k: int, v: int): string = $k & ":" & $v)
        check(t2.len == root.len)
        # check(t2 == root) # set == just checks keys, but typecheck fails
        check(t2 <= root)
        check(root <= t2)
        for k,v in revorder(t2):
            check(root.contains(k))
            check(k in root) # alt syntax using `in` template
            check(v.is(string))
            let s = split(v, {':'})
            check($k == s[0])
            check($(-k) == s[1])
        for k,v in revorder(root):
            check(t2.contains(k))
            check(v.is(int))

suite "test set funcs of bbtree.nim":

    test "toSet":
       var numbers : BBTree[int,bool] = toSet([1, 2, 3, 4, 5])
       check(numbers.contains(2))
       check(numbers.contains(4))

    test "Nim compat":
        var
            a : BBTree[string,bool] = toSet(["a", "b"])
            b : BBTree[string,bool] = toSet(["b", "c"])
            c = union(a, b)
        # `==` not working yet, so check twice, <= and >=
        check(c =?= toSet(["a", "b", "c"]))
        var d = intersection(a, b)
        check(d =?= toSet(["b"]))
        var e = difference(a, b)
        check(e =?= toSet(["a"]))
        var f = symmetricDifference(a, b)
        check(f =?= toSet(["a", "c"]))
        check(d < a and d < b)
        check((a < a) == false)
        check(d <= a and d <= b)
        check((a <= a))
        # Alias test.
        check(a + b =?= toSet(["a", "b", "c"]))
        check(a * b =?= toSet(["b"]))
        check(a - b =?= toSet(["a"]))
        check(a -+- b =?= toSet(["a", "c"]))
        check(disjoint(a, b) == false)
        check(disjoint(a, b - a) == true)

    test "Pairs as keys":
        type pair = tuple[a, b: int]
        var aa : BBTree[pair,bool]
        var bb : BBTree[pair,bool]
        var x = (a:1,b:2)
        var y = (a:3,b:4)
        aa = aa.add(x, true)
        aa = aa.add(y, true)
        bb = bb.add(x, true)
        bb = bb.add(y, true)
        check(aa =?= bb)


suite "random stress test of bbtree.nim":

    const
        STRESS_TEST_N {.intdefine.} : int = 2000
        BB_ITERATIONS {.intdefine.} : int = 2000

        MARKER = low(int64)
        chs = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"

    var
        tree : BBTree[string, int64]
        intree : array[0..STRESS_TEST_N-1, int64]
        qintree = 0
        q_ins = 0
        q_del = 0
        rand1 : Rand

    proc init_random_tree() =
        rand1 = initRand(0x987654321)
        for i in 0..<STRESS_TEST_N:
            intree[i] = MARKER
        qintree = 0;
        q_ins = 0
        q_del = 0

    proc make_random_key_val(k: int64) : (string, int64) =
        var randk = initRand(k)
        let size = rand(randk, 16) + 8
        var key = repeat(' ', size)
        for i in 0..<size:
            key[i] = chs[rand(randk,51)]
        result = (key, -k)

    proc tstput(k: int64) =
        let (key,val) = make_random_key_val(k)
        tree = tree.add(key, val)

    proc tstget(k: int64) : int64 =
        let (key,val) = make_random_key_val(k)
        discard val
        result = tree.get(key, 1)

    proc tstrem(k: int64) =
        let (key,val) = make_random_key_val(k)
        discard val
        tree = tree.del(key)

    proc do_random_tree_op()  =
        let x = rand(rand1, STRESS_TEST_N-1)
        let n = intree[x]
        if n == MARKER:
            # insert
            let k = rand(rand1, high(int64))
            tstput(k)
            intree[x] = k
            qintree += 1
            q_ins += 1
        else:
            # delete
            tstrem(n)
            intree[x] = MARKER
            qintree -= 1
            q_del += 1

    proc find_and_wipe_duplicate() : int =
        result = 0
        for i in 0..<STRESS_TEST_N:
            let n = intree[i]
            if n != MARKER:
                for j in (i+1)..<STRESS_TEST_N:
                    if n == intree[j]:
                        # duplicate
                        intree[j] = MARKER
                        qintree -= 1
                        q_ins -= 1
                        return j # > 0

    test "timed random tree iterations":
        var stop = false
        var start = cpuTime()
        write(stderr, "        ")
        init_random_tree()
        for i in 1..BB_ITERATIONS:
            if stop: break
            do_random_tree_op()
            for j in 0..<STRESS_TEST_N:
                let n = intree[j]
                if n != MARKER:
                    let v = tstget(n)
                    check(v <= 0)
                    check(v == -n)
                    if v == 1:
                        stop = true
                        break
            let sz = tree.len
            if sz != q_ins - q_del:
                let dup = find_and_wipe_duplicate()
                if dup != 0:
                    # whew!
                    echo "dup!"
            check(sz == (q_ins - q_del))
            if stop or (sz != (q_ins - q_del)):
                #fprintf(stderr, "random err: %u nodes, %ld final size\n", sz, q_ins - q_del);
                check(not stop)
                stop = true
            if i mod 1024 == 0:
                write(stderr, ".")
                check(isOrdered(tree, ""))
                check(isBalanced(tree))
        let finish = cpuTime()
        write(stderr, "\n        CPU time ", finish - start,
                      " s for ", BB_ITERATIONS, " loops, averaging ",
                       (finish - start) / toFloat(BB_ITERATIONS), " s per loop\n")
        write(stderr, "        random q: ", q_ins, " inserts, ", q_del, " deletes, ", qintree, " qintree, ",
                         q_ins - q_del, " final size\n")


#[

]#

#    test "out of bounds error is thrown on bad access":
#        let v = @[1, 2, 3]  # you can do initialization here
#        expect(IndexError):
#            discard v[4]

    # echo "suite teardown"
*/