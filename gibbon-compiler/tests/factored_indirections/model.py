#!/usr/bin/env python3
"""Expected output of each program in this directory, computed from its source
definitions.  Usage: model.py PROGRAM"""
import sys

P = 1000000007


def mk1(n):
    return ('L', 1) if n <= 0 else ('N', mk1(n - 1), mk1(n - 1))


def mk(k, n):
    return ('L', k) if n <= 0 else ('N', mk(k * 2, n - 1), mk(k * 2 + 1, n - 1))


def sum_plain(t):
    return t[1] if t[0] == 'L' else sum_plain(t[1]) + sum_plain(t[2])


def sum_w(t, w, m=None):
    if t[0] == 'L':
        return t[1] if m is None else t[1] % m
    return sum_w(t[1], w, m) + w * sum_w(t[2], w, m)


def f(t):
    return ('L', t[1] + 1) if t[0] == 'L' else ('N', f(t[1]), t[2])


def swap(t):
    return t if t[0] == 'L' else ('N', swap(t[2]), t[1])


def tup(*xs):
    return "'#(" + " ".join(map(str, xs)) + ")"


def IdTree():
    return sum_plain(mk1(4))


def RightTree():
    t = mk(1, 5)
    return sum_w(t if t[0] == 'L' else t[2], 2)


def PassThru():
    return sum_w(f(f(mk(1, 6))), 3)


def MultiBuf():
    def mkT(k, n):
        return None if n <= 0 else (k % 100, k * 1000, mkT(k * 2, n - 1), mkT(k * 2 + 1, n - 1))

    def sT(t):
        return 0 if t is None else t[0] + t[1] + sT(t[2]) + 3 * sT(t[3])

    def passT(t):
        return None if t is None else (t[0], t[1], passT(t[2]), t[3])

    return tup(sT(mkT(1, 5)), sT(passT(passT(mkT(1, 9)))))


def BigTree():
    t = mk(1, 17)
    return tup(sum_w(t, 3, 1000), sum_w(f(f(t)), 3, 1000), sum_w(swap(swap(t)), 3, 1000))


def Spine():
    # The spine is a right-nested list of (element, rest); bumpSpine adds one to
    # the final leaf and shares every element.
    n = 4000
    elems = [mk(i, i % 4) for i in range(n, 0, -1)]
    last = 0 + 2
    acc = last
    for e in reversed(elems):
        acc = (7 * sum_w(e, 3, 1000) + 5 * acc) % P
    return acc


def GcShare():
    acc = 0
    for i in range(200, 0, -1):
        acc = (acc + sum_w(f(mk(i, 10)), 3, 1000)) % P
    t = f(mk(1, 12))
    return tup(acc, sum_w(t, 3, 1000), sum_w(f(t), 3, 1000))


def GcSafe():
    t = f(mk(1, 12))
    return tup(sum_w(mk(5, 15), 3, 1000) + sum_w(mk(6, 15), 3, 1000),
               sum_w(t, 3, 1000), sum_w(f(t), 3, 1000))


def MixedLayout():
    return sum((n + 1) + (n + 1) for n in range(1, 101))


if __name__ == '__main__':
    sys.setrecursionlimit(100000)
    print(globals()[sys.argv[1]]())
