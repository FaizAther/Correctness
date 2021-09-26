def Tangent(r, x):
    found = False
    n = 0
    while n != len(r) and not found:
        f = BinarySearch(x, r[n])
        if (f != len(x) and x[f] == r[n]):
            found = True
        else:
            n = n + 1
    assert (not found and n == len(r)) or \
        (found and n != len(r) and r[n] == x[f])
    return found


def BinarySearch(a, circle):
    lo, hi = 0, len(a)
    while lo < hi:
        mid = int((lo + hi) / 2)
        if (a[lo] > circle):
            hi = lo
        elif (a[hi-1] < circle):
            lo = hi
        elif (a[mid] < circle):
            lo = mid + 1
        else:
            hi = mid
    n = lo
    return n


def main():
    r = []
    x = [1, 2, 3, 4, 5, 6, 7, 8, 9]
    b = Tangent(r, x)
    assert not b

    r = [1, 2, 3, 4, 5, 6, 7, 8, 9]
    x = []
    b = Tangent(r, x)
    assert not b

    r = [1000, 12, 22, 55, 412, 10, 556]
    x = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
    b = Tangent(r, x)
    assert b

    r = [1000, 12, 22, 55, 412, 10, 556]
    x = [1, 2, 3, 4, 5, 6, 7, 8, 9]
    b = Tangent(r, x)
    assert not b

    r = [10, 10, 10, 10, 10, 10, 50, 10, 10, 10, 10, 50, 10]
    x = [50]
    b = Tangent(r, x)
    assert b


if __name__ == "__main__":
    main()
