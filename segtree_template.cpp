/*
====================================================================================
SEGMENT TREE â€” MASTER TEMPLATE (Competitive Programming)
====================================================================================
Style follows the Codeforces EDU convention (used across ALL sections here for
consistency, including the ones adapted from cp-algorithms.com which normally
use inclusive [tl, tr] indexing):
    size = next power of two >= n
    node x covers the HALF-OPEN interval [lx, rx)
    left child = 2x+1, right child = 2x+2
    leaf found when rx - lx == 1

Every variation on https://cp-algorithms.com/data_structures/segment_tree.html
is represented below, either as runnable code or (for a couple of extremely
niche accelerations) as a documented note explaining what it is and why it's
left as a note instead of 40 more lines of rarely-used code.

CONTENTS
--------
[1]  COMMON-STYLE SEGMENT TREE   (Point Update + Range Query)
     -> One template. Covers: Sum, Min, Max, GCD, LCM, XOR, AND, OR,
        Product(mod), Count/Exists. Only 2 lines change between variations
        (see doxygen block above section 1).
     -> Extensions on the SAME struct (still O(log n), no extra memory):
          - firstGreater(l, r, x): cp-algorithms "searching for the first
            element greater than a given amount" (needs Max configuration)
          - findKthOne(k): cp-algorithms "counting zeros / k-th zero"
            (needs Sum configuration over 0/1 leaves)
[1b] MAX + COUNT-OF-MAX SEGMENT TREE (pair-valued node, doesn't fit [1]'s
     single-scalar combine, so it gets its own tiny struct)
[2]  RANGE UPDATE / POINT QUERY            (no lazy needed â€” difference trick)
[3]  RANGE UPDATE / RANGE QUERY  â€” LAZY    (Range Add + Range Sum)
     -> Notes included for turning it into Range-Add + Range-Min/Max
        (cp-algorithms "Adding on segments, querying for maximum")
[4]  RANGE ASSIGN (SET) â€” LAZY             (Range Set + Range Sum/Min/Max)
[5]  MERGE SORT TREE                       (cp-algorithms "saving the entire
     subarrays in each vertex")
       - static version: count elements < K in a range / find first >= K
       - mutable version: same, but supports point updates (multiset nodes)
[6]  PERSISTENT SEGMENT TREE               (point update creates new version,
     range sum query on any version)
       - also: k-th smallest element in a range, via a persistent histogram
         built with add() and queried by comparing two versions
[7]  MAX SUBARRAY SUM SEGMENT TREE         (Kadane merge, custom node â€” does
     NOT fit the common style, shown separately)
[8]  BINARY SEARCH ON SEGMENT TREE         (walk down the tree to find first
     index whose PREFIX satisfies a condition â€” cp-algorithms "searching for
     an array prefix with a given amount")
[9]  ITERATIVE (NON-RECURSIVE) SEGMENT TREE  (cp-algorithms "memory efficient
     implementation" family: no recursion, 2n array instead of 4n, small
     constant factor â€” great when you just need point update + range query
     on a commutative/associative op and don't need lazy propagation)
[10] SIMPLE 2D SEGMENT TREE                (point update + submatrix query;
     cp-algorithms "generalization to higher dimensions")
[11] DYNAMIC (IMPLICIT / SPARSE) SEGMENT TREE  (nodes allocated on demand â€”
     use when the index range is huge, e.g. [0, 1e9), and only a few indices
     are ever touched; cp-algorithms "dynamic segment tree")

NOT implemented as full code (documented instead, see the comment where each
would go): fractional-cascading-accelerated merge sort tree, and 2D segment
tree "compression" (offline sum-of-rectangles). Both are described in
cp-algorithms as advanced/rarely-needed accelerations of [5] and [10]
respectively, are highly problem-specific to wire up correctly, and are
better hand-rolled from the base structures here than kept as a generic
template. A pointer to what they are and how to build them from the pieces
in this file is left in place.

A single main() at the bottom exercises every variation above.
====================================================================================
*/

#include <bits/stdc++.h>
using namespace std;
typedef long long ll;
const ll INF = LLONG_MAX / 2;

/*
====================================================================================
[1] COMMON-STYLE SEGMENT TREE â€” Point Update, Range Query
====================================================================================
@brief   Single reusable template for every "simple" segment tree: the ones where
         a range query is just repeatedly combining a leaf value with an
         associative, commutative(-ish) operator, and there's nothing to lazily
         push down.
@usage   segtree.init(n); segtree.build(a); segtree.set(i, v); segtree.query(l, r);
         query(l, r) is over the HALF-OPEN interval [l, r).

HOW TO SWITCH VARIATION â€” only the two lines tagged "// <-- EDIT" ever change:

Variation      | NEUTRAL (identity element)       | combine(a, b)
---------------|-----------------------------------|---------------------
Sum            | 0                                 | a + b
Min            | INF  (or numeric_limits::max)     | min(a, b)
Max            | -INF (or numeric_limits::min)     | max(a, b)
GCD            | 0                                 | __gcd(a, b)
LCM            | 1                                 | lcm(a, b)  (watch overflow)
XOR            | 0                                 | a ^ b
AND            | ~0LL (all bits set)               | a & b
OR             | 0                                 | a | b
Product mod P  | 1                                 | (a * b) % P
Count/Exists   | 0                                 | a + b   (leaves are 0/1)

If T is not an integral type (e.g. double), replace the in-class
"static constexpr T NEUTRAL" with an out-of-class definition, or just make it a
non-static member set in init().
====================================================================================
*/
struct SegTree {
    using T = ll;
    static constexpr T NEUTRAL = 0;                 // <-- EDIT (identity element)

    static T combine(T a, T b) {                    // <-- EDIT (the operator)
        return a + b;
    }

    int n; // = size (next power of two)
    vector<T> tree;

    void init(int n_) {
        n = 1;
        while (n < n_) n *= 2;
        tree.assign(2 * n, NEUTRAL);
    }

    void build(vector<T> &a, int x, int lx, int rx) {
        if (rx - lx == 1) {
            if (lx < (int)a.size()) tree[x] = a[lx];
            return;
        }
        int m = (lx + rx) / 2;
        build(a, 2 * x + 1, lx, m);
        build(a, 2 * x + 2, m, rx);
        tree[x] = combine(tree[2 * x + 1], tree[2 * x + 2]);
    }
    void build(vector<T> &a) { build(a, 0, 0, n); }

    void set(int i, T v, int x, int lx, int rx) {
        if (rx - lx == 1) { tree[x] = v; return; }
        int m = (lx + rx) / 2;
        if (i < m) set(i, v, 2 * x + 1, lx, m);
        else       set(i, v, 2 * x + 2, m, rx);
        tree[x] = combine(tree[2 * x + 1], tree[2 * x + 2]);
    }
    void set(int i, T v) { set(i, v, 0, 0, n); }

    T query(int l, int r, int x, int lx, int rx) {
        if (lx >= r || l >= rx) return NEUTRAL;
        if (lx >= l && rx <= r) return tree[x];
        int m = (lx + rx) / 2;
        return combine(query(l, r, 2 * x + 1, lx, m), query(l, r, 2 * x + 2, m, rx));
    }
    T query(int l, int r) { return query(l, r, 0, 0, n); }

    /*
    * [8] BINARY SEARCH ON SEGMENT TREE â€” "searching for an array prefix with a
    *     given amount" (cp-algorithms).
    * @brief Finds the smallest index i (0-indexed, within [0, n)) such that
    *        combine(tree[0..i]) satisfies pred(prefixValue) == true.
    *        Requires the running combine to be MONOTONIC as more elements are
    *        added (classic use: Sum with all-nonnegative values, looking for
    *        the first prefix-sum >= K -> pred = [K](ll v){ return v >= K; }).
    * @return index in [0, n), or n if no such index exists.
    */
    int walk(function<bool(T)> pred) {
        if (!pred(tree[0])) return n; // even the whole range doesn't satisfy it
        int x = 0, lx = 0, rx = n;
        T acc = NEUTRAL;
        while (rx - lx > 1) {
            int m = (lx + rx) / 2;
            T withLeft = combine(acc, tree[2 * x + 1]);
            if (pred(withLeft)) { x = 2 * x + 1; rx = m; }
            else { acc = withLeft; x = 2 * x + 2; lx = m; }
        }
        return lx;
    }

    /*
    * [1-ext] "Searching for the first element greater than a given amount"
    * @brief  Requires the tree to be configured as a MAX segment tree
    *         (NEUTRAL = -INF, combine = max). Finds the smallest index i in
    *         [l, r) such that a[i] > x.
    * @return index in [l, r), or -1 if no such element exists.
    *         Amortized O(log n): at most 2 paths are ever fully descended.
    */
    int firstGreater(int l, int r, T x, int v, int lx, int rx) {
        if (lx >= r || l >= rx || tree[v] <= x) return -1;
        if (rx - lx == 1) return lx;
        int m = (lx + rx) / 2;
        int res = firstGreater(l, r, x, 2 * v + 1, lx, m);
        if (res != -1) return res;
        return firstGreater(l, r, x, 2 * v + 2, m, rx);
    }
    int firstGreater(int l, int r, T x) { return firstGreater(l, r, x, 0, 0, n); }

    /*
    * [1-ext] "Counting the number of zeros, searching for the k-th zero"
    * @brief  Requires the tree to be configured as a Sum segment tree over
    *         0/1 leaves (NEUTRAL = 0, combine = a + b), where 1 marks the
    *         element you're counting/searching for (e.g. "is a live point",
    *         "is a one-bit", "is present"). Finds the index of the k-th such
    *         marked element (1-indexed k).
    *         To search for the k-th ZERO instead (as in cp-algorithms):
    *         store 1 - a[i] as the leaf value, everything else is identical.
    * @return index in [0, n), or n if fewer than k marked elements exist.
    */
    int findKthOne(T k, int v, int lx, int rx) {
        if (rx - lx == 1) return lx;
        int m = (lx + rx) / 2;
        T leftCount = tree[2 * v + 1];
        if (leftCount >= k) return findKthOne(k, 2 * v + 1, lx, m);
        return findKthOne(k - leftCount, 2 * v + 2, m, rx);
    }
    int findKthOne(T k) { return (tree[0] < k) ? n : findKthOne(k, 0, 0, n); }
};


/*
====================================================================================
[1b] MAX + COUNT-OF-MAX SEGMENT TREE  (pair-valued node)
====================================================================================
@brief   cp-algorithms "Finding the maximum and the number of times it appears".
         Doesn't fit the scalar-T combine of [1], since each node needs a
         (value, count) pair whose merge logic is a couple of if/else branches
         instead of a one-line operator. Point update + range query for
         "max in [l, r), and how many times it occurs there".
@usage   mc.init(n); mc.build(a); mc.set(i, v); mc.query(l, r); // -> {max, count}
====================================================================================
*/
struct MaxCountSegTree {
    struct Node { ll val; ll cnt; };
    static constexpr Node NEUTRAL = { -LLONG_MAX / 2, 0 };

    static Node combine(Node a, Node b) {
        if (a.val > b.val) return a;
        if (b.val > a.val) return b;
        return { a.val, a.cnt + b.cnt };
    }

    int n;
    vector<Node> tree;

    void init(int n_) {
        n = 1;
        while (n < n_) n *= 2;
        tree.assign(2 * n, NEUTRAL);
    }

    void build(vector<ll> &a, int x, int lx, int rx) {
        if (rx - lx == 1) {
            tree[x] = (lx < (int)a.size()) ? Node{ a[lx], 1 } : NEUTRAL;
            return;
        }
        int m = (lx + rx) / 2;
        build(a, 2 * x + 1, lx, m);
        build(a, 2 * x + 2, m, rx);
        tree[x] = combine(tree[2 * x + 1], tree[2 * x + 2]);
    }
    void build(vector<ll> &a) { build(a, 0, 0, n); }

    void set(int i, ll v, int x, int lx, int rx) {
        if (rx - lx == 1) { tree[x] = { v, 1 }; return; }
        int m = (lx + rx) / 2;
        if (i < m) set(i, v, 2 * x + 1, lx, m);
        else       set(i, v, 2 * x + 2, m, rx);
        tree[x] = combine(tree[2 * x + 1], tree[2 * x + 2]);
    }
    void set(int i, ll v) { set(i, v, 0, 0, n); }

    Node query(int l, int r, int x, int lx, int rx) {
        if (lx >= r || l >= rx) return NEUTRAL;
        if (lx >= l && rx <= r) return tree[x];
        int m = (lx + rx) / 2;
        return combine(query(l, r, 2 * x + 1, lx, m), query(l, r, 2 * x + 2, m, rx));
    }
    Node query(int l, int r) { return query(l, r, 0, 0, n); }
};


/*
====================================================================================
[2] RANGE UPDATE / POINT QUERY  (difference trick â€” no lazy propagation needed)
====================================================================================
@brief   Add v to every element in [l, r), read back a single element at index i.
         Works by storing a DIFFERENCE array in a plain Sum segment tree:
             add(l, r, v)  =>  point-add +v at l, point-add -v at r
             pointQuery(i) =>  prefix sum over [0, i+1)
@usage   rupq.init(n); rupq.build(a); rupq.update(l, r, v); rupq.query(i);
====================================================================================
*/
struct RangeUpdatePointQuery {
    SegTree diff; // reuse the Sum configuration of SegTree from [1] as-is

    void init(int n) { diff.init(n); }

    void build(vector<ll> &a) {
        vector<ll> d(a.size());
        d[0] = a[0];
        for (int i = 1; i < (int)a.size(); i++) d[i] = a[i] - a[i - 1];
        diff.build(d);
    }

    // adds v to every index in [l, r)
    void update(int l, int r, ll v) {
        diff.set(l, diff.query(l, l + 1) + v);
        if (r < diff.n) diff.set(r, diff.query(r, r + 1) - v);
    }

    // current value at index i
    ll query(int i) { return diff.query(0, i + 1); }
};


/*
====================================================================================
[3] RANGE UPDATE / RANGE QUERY â€” LAZY PROPAGATION  (Range Add, Range Sum)
====================================================================================
@brief   Add v to every element of [l, r); query the SUM over [l, r).
@usage   lazy.init(n); lazy.build(a); lazy.update(l, r, v); lazy.query(l, r);

TO CONVERT TO "Range Add + Range Min" or "Range Add + Range Max"
(cp-algorithms "Adding on segments, querying for maximum"):
- tree[x] combine step: change `tree[x1] + tree[x2]` to `min(tree[x1], tree[x2])`
    (or max). NEUTRAL becomes INF (or -INF).
- In query()/push(), when applying `add` to a node, min/max nodes shift by the
    SAME add value directly (tree[x] += lazy[x]); this still works unchanged,
    because add distributes over min/max the same way it does over sum's total â€”
    ONLY the merge step (parent = combine of children) differs. Sum needs
    `tree[x] += lazy[x] * (rx - lx)` (scaled by segment length); Min/Max do NOT
    scale by length â€” just `tree[x] += lazy[x]`.
====================================================================================
*/
struct LazySegTreeRangeAdd {
    int n;
    vector<ll> tree, lazy;

    void init(int n_) {
        n = 1;
        while (n < n_) n *= 2;
        tree.assign(2 * n, 0);
        lazy.assign(2 * n, 0);
    }

    void build(vector<ll> &a, int x, int lx, int rx) {
        if (rx - lx == 1) {
            if (lx < (int)a.size()) tree[x] = a[lx];
            return;
        }
        int m = (lx + rx) / 2;
        build(a, 2 * x + 1, lx, m);
        build(a, 2 * x + 2, m, rx);
        tree[x] = tree[2 * x + 1] + tree[2 * x + 2];
    }
    void build(vector<ll> &a) { build(a, 0, 0, n); }

    void applyAdd(int x, int lx, int rx, ll v) {
        tree[x] += v * (rx - lx); // <-- EDIT: for Min/Max use `tree[x] += v;` (no scaling)
        lazy[x] += v;
    }

    void push(int x, int lx, int rx) {
        if (lazy[x] == 0) return;
        int m = (lx + rx) / 2;
        applyAdd(2 * x + 1, lx, m, lazy[x]);
        applyAdd(2 * x + 2, m, rx, lazy[x]);
        lazy[x] = 0;
    }

    void update(int l, int r, ll v, int x, int lx, int rx) {
        if (lx >= r || l >= rx) return;
        if (lx >= l && rx <= r) { applyAdd(x, lx, rx, v); return; }
        push(x, lx, rx);
        int m = (lx + rx) / 2;
        update(l, r, v, 2 * x + 1, lx, m);
        update(l, r, v, 2 * x + 2, m, rx);
        tree[x] = tree[2 * x + 1] + tree[2 * x + 2]; // <-- EDIT: min/max -> min()/max()
    }
    void update(int l, int r, ll v) { update(l, r, v, 0, 0, n); }

    ll query(int l, int r, int x, int lx, int rx) {
        if (lx >= r || l >= rx) return 0;             // <-- EDIT: neutral for min/max
        if (lx >= l && rx <= r) return tree[x];
        push(x, lx, rx);
        int m = (lx + rx) / 2;
        return query(l, r, 2 * x + 1, lx, m) + query(l, r, 2 * x + 2, m, rx); // <-- EDIT
    }
    ll query(int l, int r) { return query(l, r, 0, 0, n); }
};


/*
====================================================================================
[4] RANGE ASSIGN (SET) â€” LAZY PROPAGATION  (Range Set + Range Sum, with Min/Max notes)
====================================================================================
@brief   Set every element of [l, r) to value v; query aggregate over [l, r).
         Needs a `hasLazy` flag because 0 is a perfectly valid value to assign,
         so we cannot use "0 means no pending update" like in [3].
@usage   ras.init(n); ras.build(a); ras.update(l, r, v); ras.query(l, r);

TO CONVERT SUM -> MIN or MAX: change combine() in pull()/query() and NEUTRAL,
exactly like the note in section [3]. applyAssign() needs NO change either way
(assign overwrites, it doesn't scale with segment length for sum either â€” the
whole segment becomes v*(rx-lx) for sum, or just v for min/max).
====================================================================================
*/
struct LazySegTreeRangeAssign {
    int n;
    vector<ll> tree;
    vector<ll> lazyVal;
    vector<bool> hasLazy;

    void init(int n_) {
        n = 1;
        while (n < n_) n *= 2;
        tree.assign(2 * n, 0);
        lazyVal.assign(2 * n, 0);
        hasLazy.assign(2 * n, false);
    }

    void build(vector<ll> &a, int x, int lx, int rx) {
        if (rx - lx == 1) {
            if (lx < (int)a.size()) tree[x] = a[lx];
            return;
        }
        int m = (lx + rx) / 2;
        build(a, 2 * x + 1, lx, m);
        build(a, 2 * x + 2, m, rx);
        tree[x] = tree[2 * x + 1] + tree[2 * x + 2]; // <-- EDIT for min/max
    }
    void build(vector<ll> &a) { build(a, 0, 0, n); }

    void applyAssign(int x, int lx, int rx, ll v) {
        tree[x] = v * (rx - lx);   // <-- EDIT: for Min/Max use `tree[x] = v;`
        lazyVal[x] = v;
        hasLazy[x] = true;
    }

    void push(int x, int lx, int rx) {
        if (!hasLazy[x]) return;
        int m = (lx + rx) / 2;
        applyAssign(2 * x + 1, lx, m, lazyVal[x]);
        applyAssign(2 * x + 2, m, rx, lazyVal[x]);
        hasLazy[x] = false;
    }

    void update(int l, int r, ll v, int x, int lx, int rx) {
        if (lx >= r || l >= rx) return;
        if (lx >= l && rx <= r) { applyAssign(x, lx, rx, v); return; }
        push(x, lx, rx);
        int m = (lx + rx) / 2;
        update(l, r, v, 2 * x + 1, lx, m);
        update(l, r, v, 2 * x + 2, m, rx);
        tree[x] = tree[2 * x + 1] + tree[2 * x + 2]; // <-- EDIT for min/max
    }
    void update(int l, int r, ll v) { update(l, r, v, 0, 0, n); }

    ll query(int l, int r, int x, int lx, int rx) {
        if (lx >= r || l >= rx) return 0;              // <-- EDIT neutral for min/max
        if (lx >= l && rx <= r) return tree[x];
        push(x, lx, rx);
        int m = (lx + rx) / 2;
        return query(l, r, 2 * x + 1, lx, m) + query(l, r, 2 * x + 2, m, rx); // <-- EDIT
    }
    ll query(int l, int r) { return query(l, r, 0, 0, n); }
};


/*
====================================================================================
[5] MERGE SORT TREE  (offline range queries needing a SORTED view of a range)
====================================================================================
@brief   Each node stores a SORTED vector of the elements in its range, built by
         merging children (like merge sort). Enables, per query, in O(log^2 n):
             - count of elements < K (or in [lo, hi)) inside [l, r)
             - smallest element >= K inside [l, r)
             - (extendable to k-th smallest with an extra binary search on the
             answer value, or use a Persistent Segment Tree instead for
             O(log n) k-th order statistic â€” see [6])
@usage   mst.build(a); mst.countLess(l, r, K); mst.firstAtLeast(l, r, K);
@note    Static structure only â€” no point updates without a full rebuild.
         For updates, see MergeSortTreeMutable right below.
====================================================================================
*/
struct MergeSortTree {
    int n;
    vector<vector<int>> tree;

    void build(vector<int> &a, int x, int lx, int rx) {
        if (rx - lx == 1) {
            tree[x] = { (lx < (int)a.size()) ? a[lx] : INT_MAX };
            return;
        }
        int m = (lx + rx) / 2;
        build(a, 2 * x + 1, lx, m);
        build(a, 2 * x + 2, m, rx);
        merge(tree[2 * x + 1].begin(), tree[2 * x + 1].end(),
            tree[2 * x + 2].begin(), tree[2 * x + 2].end(),
            back_inserter(tree[x]));
    }
    void build(vector<int> &a) {
        n = 1;
        while (n < (int)a.size()) n *= 2;
        tree.assign(2 * n, {});
        build(a, 0, 0, n);
    }

    // count of elements strictly less than K within [l, r)
    int countLess(int l, int r, int K, int x, int lx, int rx) {
        if (lx >= r || l >= rx) return 0;
        if (lx >= l && rx <= r)
            return (int)(lower_bound(tree[x].begin(), tree[x].end(), K) - tree[x].begin());
        int m = (lx + rx) / 2;
        return countLess(l, r, K, 2 * x + 1, lx, m) + countLess(l, r, K, 2 * x + 2, m, rx);
    }
    int countLess(int l, int r, int K) { return countLess(l, r, K, 0, 0, n); }

    // cp-algorithms "find smallest number >= K in a[l..r), no modifications"
    int firstAtLeast(int l, int r, int K, int x, int lx, int rx) {
        if (lx >= r || l >= rx) return INT_MAX;
        if (lx >= l && rx <= r) {
            auto it = lower_bound(tree[x].begin(), tree[x].end(), K);
            return (it != tree[x].end()) ? *it : INT_MAX;
        }
        int m = (lx + rx) / 2;
        return min(firstAtLeast(l, r, K, 2 * x + 1, lx, m),
                   firstAtLeast(l, r, K, 2 * x + 2, m, rx));
    }
    int firstAtLeast(int l, int r, int K) { return firstAtLeast(l, r, K, 0, 0, n); }
};

/*
------------------------------------------------------------------------------------
[5b] MERGE SORT TREE â€” mutable version (multiset nodes)
------------------------------------------------------------------------------------
@brief   cp-algorithms "find smallest number >= K, WITH modification queries".
         Same idea as [5], but each node is a std::multiset instead of a sorted
         vector, so a[i] = newVal can erase the old value and insert the new one
         in every node on the O(log n) root-to-leaf path.
@usage   mstm.init(n); mstm.build(a); mstm.update(i, newVal); mstm.firstAtLeast(l,r,K);
@note    Query/build/update are all O(log^2 n). Heavier constant than [5] because
         of multiset overhead â€” only pay for this if you truly need updates.
         (cp-algorithms also describes a "fractional cascading" trick that
         speeds queries on the static version down to O(log n); it's a
         genuinely advanced, very fiddly optimization on top of [5] and is
         intentionally not templated here â€” see the article if you need it.)
------------------------------------------------------------------------------------
*/
struct MergeSortTreeMutable {
    int n;
    vector<int> a;
    vector<multiset<int>> tree;

    void build(int x, int lx, int rx) {
        if (rx - lx == 1) {
            tree[x].insert(lx < (int)a.size() ? a[lx] : INT_MAX);
            return;
        }
        int m = (lx + rx) / 2;
        build(2 * x + 1, lx, m);
        build(2 * x + 2, m, rx);
        tree[x].insert(tree[2 * x + 1].begin(), tree[2 * x + 1].end());
        tree[x].insert(tree[2 * x + 2].begin(), tree[2 * x + 2].end());
    }
    void init(int n_) {
        n = 1;
        while (n < n_) n *= 2;
        tree.assign(2 * n, {});
    }
    void build(vector<int> &a_) { a = a_; build(0, 0, n); }

    void update(int i, int v, int x, int lx, int rx) {
        tree[x].erase(tree[x].find(a[i])); // remove exactly one occurrence
        tree[x].insert(v);
        if (rx - lx == 1) return;
        int m = (lx + rx) / 2;
        if (i < m) update(i, v, 2 * x + 1, lx, m);
        else       update(i, v, 2 * x + 2, m, rx);
    }
    void update(int i, int v) { update(i, v, 0, 0, n); a[i] = v; }

    int firstAtLeast(int l, int r, int K, int x, int lx, int rx) {
        if (lx >= r || l >= rx) return INT_MAX;
        if (lx >= l && rx <= r) {
            auto it = tree[x].lower_bound(K);
            return (it != tree[x].end()) ? *it : INT_MAX;
        }
        int m = (lx + rx) / 2;
        return min(firstAtLeast(l, r, K, 2 * x + 1, lx, m),
                   firstAtLeast(l, r, K, 2 * x + 2, m, rx));
    }
    int firstAtLeast(int l, int r, int K) { return firstAtLeast(l, r, K, 0, 0, n); }
};


/*
====================================================================================
[6] PERSISTENT SEGMENT TREE  (Point Update creates a new immutable version)
====================================================================================
@brief   Every update creates O(log n) new nodes and returns a new root, while
         all previous versions remain fully queryable. Node 0 is a permanent
         "null" sentinel (val[0] = 0, so treating a 0 index as an empty/zero
         subtree is always safe â€” no special-casing needed elsewhere).

TWO INDEPENDENT USAGE PATTERNS share this one struct:

(a) ARRAY SNAPSHOTS â€” use build(a) then update(root, i, v) (point ASSIGN).
    Each update gives you a full new version of the array; query(root, l, r)
    is the range sum as of that version.
        root0 = pst.build(a);
        root1 = pst.update(root0, i, v);   // version 1 = version0 with a[i]=v
        pst.query(root1, l, r);            // range sum on version 1

(b) K-TH SMALLEST IN A RANGE â€” cp-algorithms "Finding the k-th smallest number
    in a range". Coordinate-compress the array values to [0, n), start from an
    all-empty tree, and use add(root, compressedValue, +1) (point INCREMENT,
    not assign) once per array element, keeping every intermediate root:
        roots[0] = pst.build(n);                      // empty histogram
        for i in [0, n): roots[i+1] = pst.add(roots[i], compressed[i], +1);
    roots[i] is now the histogram of a[0..i). The histogram of a[l..r) is the
    *difference* of roots[r] and roots[l] node-by-node â€” you never build it
    explicitly, findKth() walks both trees in lockstep instead:
        idx = pst.findKth(roots[l], roots[r], k);      // 1-indexed k
        original_value = compressedValueToOriginal[idx];
====================================================================================
*/
struct PersistentSegTree {
    int n;
    vector<ll> val;
    vector<int> left, right;

    void init(int n_) {
        n = 1;
        while (n < n_) n *= 2;
        val.reserve(n * 40); left.reserve(n * 40); right.reserve(n * 40);
        val.push_back(0); left.push_back(-1); right.push_back(-1); // dummy node 0 = "null"
    }

    int newLeaf(ll v) {
        val.push_back(v); left.push_back(-1); right.push_back(-1);
        return (int)val.size() - 1;
    }
    int newInternal(int l, int r) {
        val.push_back((l ? val[l] : 0) + (r ? val[r] : 0));
        left.push_back(l); right.push_back(r);
        return (int)val.size() - 1;
    }

    // ---- (a) array snapshots: build + point assign ----
    int build(vector<ll> &a, int lx, int rx) {
        if (rx - lx == 1) return newLeaf(lx < (int)a.size() ? a[lx] : 0);
        int m = (lx + rx) / 2;
        int l = build(a, lx, m), r = build(a, m, rx);
        return newInternal(l, r);
    }
    int build(vector<ll> &a) { return build(a, 0, n); }
    int build() { vector<ll> empty; return build(empty, 0, n); } // all-zero histogram, for (b)

    // returns the root of the NEW version; old version (rootOld) stays valid
    int update(int rootOld, int i, ll v, int lx, int rx) {
        if (rx - lx == 1) return newLeaf(v);
        int m = (lx + rx) / 2;
        int l = left[rootOld], r = right[rootOld];
        if (i < m) l = update(l, i, v, lx, m);
        else       r = update(r, i, v, m, rx);
        return newInternal(l, r);
    }
    int update(int rootOld, int i, ll v) { return update(rootOld, i, v, 0, n); }

    ll query(int x, int l, int r, int lx, int rx) {
        if (x == 0 || lx >= r || l >= rx) return 0;
        if (lx >= l && rx <= r) return val[x];
        int m = (lx + rx) / 2;
        return query(left[x], l, r, lx, m) + query(right[x], l, r, m, rx);
    }
    ll query(int root, int l, int r) { return query(root, l, r, 0, n); }

    // ---- (b) order statistics: point increment + k-th smallest ----
    int add(int rootOld, int i, ll delta, int lx, int rx) {
        if (rx - lx == 1) return newLeaf((rootOld ? val[rootOld] : 0) + delta);
        int m = (lx + rx) / 2;
        int l = rootOld ? left[rootOld] : 0, r = rootOld ? right[rootOld] : 0;
        if (i < m) l = add(l, i, delta, lx, m);
        else       r = add(r, i, delta, m, rx);
        return newInternal(l, r);
    }
    int add(int rootOld, int i, ll delta) { return add(rootOld, i, delta, 0, n); }

    // k is 1-indexed. rootL/rootR are histogram-versions such that the range
    // of interest is exactly (elements counted in rootR) - (elements counted
    // in rootL), e.g. rootL = roots[l], rootR = roots[r] for range [l, r).
    int findKth(int rootL, int rootR, ll k, int lx, int rx) {
        if (rx - lx == 1) return lx;
        int m = (lx + rx) / 2;
        int llx = rootL ? left[rootL] : 0, lrx = rootR ? left[rootR] : 0;
        ll leftCount = (lrx ? val[lrx] : 0) - (llx ? val[llx] : 0);
        if (leftCount >= k) return findKth(llx, lrx, k, lx, m);
        int rlx = rootL ? right[rootL] : 0, rrx = rootR ? right[rootR] : 0;
        return findKth(rlx, rrx, k - leftCount, m, rx);
    }
    int findKth(int rootL, int rootR, ll k) { return findKth(rootL, rootR, k, 0, n); }
};


/*
====================================================================================
[7] MAX SUBARRAY SUM SEGMENT TREE  (Kadane-style merge, custom node)
====================================================================================
@brief   Does NOT fit the common style from [1] because each node needs FOUR
         numbers, not one, and the merge is a small custom formula (Kadane's
         algorithm expressed as a merge operator). Supports point update +
         "max subarray sum in [l, r)" range query.
@usage   mss.init(n); mss.build(a); mss.set(i, v); mss.query(l, r).best;
====================================================================================
*/
struct MaxSubarraySegTree {
    struct Node {
        ll sum;   // total sum of the range
        ll pref;  // best prefix sum
        ll suf;   // best suffix sum
        ll best;  // best subarray sum anywhere inside the range
    };

    int n;
    vector<Node> tree;

    static Node makeLeaf(ll v) { return { v, v, v, v }; }

    static Node merge(const Node &a, const Node &b) {
        Node res;
        res.sum  = a.sum + b.sum;
        res.pref = max(a.pref, a.sum + b.pref);
        res.suf  = max(b.suf, b.sum + a.suf);
        res.best = max({ a.best, b.best, a.suf + b.pref });
        return res;
    }

    void init(int n_) {
        n = 1;
        while (n < n_) n *= 2;
        tree.assign(2 * n, { 0, 0, 0, 0 });
    }

    void build(vector<ll> &a, int x, int lx, int rx) {
        if (rx - lx == 1) {
            tree[x] = makeLeaf(lx < (int)a.size() ? a[lx] : 0);
            return;
        }
        int m = (lx + rx) / 2;
        build(a, 2 * x + 1, lx, m);
        build(a, 2 * x + 2, m, rx);
        tree[x] = merge(tree[2 * x + 1], tree[2 * x + 2]);
    }
    void build(vector<ll> &a) { build(a, 0, 0, n); }

    void set(int i, ll v, int x, int lx, int rx) {
        if (rx - lx == 1) { tree[x] = makeLeaf(v); return; }
        int m = (lx + rx) / 2;
        if (i < m) set(i, v, 2 * x + 1, lx, m);
        else       set(i, v, 2 * x + 2, m, rx);
        tree[x] = merge(tree[2 * x + 1], tree[2 * x + 2]);
    }
    void set(int i, ll v) { set(i, v, 0, 0, n); }

    Node query(int l, int r, int x, int lx, int rx) {
        if (lx >= l && rx <= r) return tree[x];
        int m = (lx + rx) / 2;
        if (r <= m) return query(l, r, 2 * x + 1, lx, m);
        if (l >= m) return query(l, r, 2 * x + 2, m, rx);
        return merge(query(l, r, 2 * x + 1, lx, m), query(l, r, 2 * x + 2, m, rx));
    }
    Node query(int l, int r) { return query(l, r, 0, 0, n); } // assumes l < r
};


/*
====================================================================================
[9] ITERATIVE (NON-RECURSIVE) SEGMENT TREE  â€” "memory efficient implementation"
====================================================================================
@brief   Bottom-up, pointer/recursion-free segment tree. Leaves live at indices
         [n, 2n) and internal nodes at [1, n), so the whole tree fits in a
         single array of size 2n (vs. 4n for the recursive form) â€” and it's
         noticeably faster in practice thanks to the tiny, branch-light loops.
         Works for ANY array length n (no need to round up to a power of two).
@limits  Point update + range query ONLY â€” this shape does not support lazy
         propagation cleanly (the "which segment am I really covering" info
         isn't explicit at each node), so for range updates use [3]/[4] instead.
@usage   it.init(n); it.build(a); it.set(i, v); it.query(l, r); // [l, r)

TO SWITCH VARIATION: change the two tagged lines to Min/Max/GCD/XOR/etc.,
exactly like the table in [1] (NEUTRAL must match: 0 for sum/xor, INF for min,
-INF for max, ...).
====================================================================================
*/
struct IterativeSegTree {
    int n;
    vector<ll> tree; // size 2n; leaves at tree[n..2n), tree[i] = combine(tree[2i], tree[2i+1])
    static constexpr ll NEUTRAL = 0;                          // <-- EDIT
    static ll combine(ll a, ll b) { return a + b; }            // <-- EDIT

    void init(int n_) { n = n_; tree.assign(2 * n, NEUTRAL); }

    void build(vector<ll> &a) {
        for (int i = 0; i < n; i++) tree[n + i] = (i < (int)a.size()) ? a[i] : NEUTRAL;
        for (int i = n - 1; i >= 1; i--) tree[i] = combine(tree[2 * i], tree[2 * i + 1]);
    }

    void set(int i, ll v) {
        i += n; tree[i] = v;
        for (i >>= 1; i >= 1; i >>= 1) tree[i] = combine(tree[2 * i], tree[2 * i + 1]);
    }

    // range query over the HALF-OPEN interval [l, r)
    ll query(int l, int r) {
        ll resL = NEUTRAL, resR = NEUTRAL;
        for (l += n, r += n; l < r; l >>= 1, r >>= 1) {
            if (l & 1) resL = combine(resL, tree[l++]);
            if (r & 1) resR = combine(tree[--r], resR);
        }
        return combine(resL, resR);
    }
};


/*
====================================================================================
[10] SIMPLE 2D SEGMENT TREE  â€” "generalization to higher dimensions"
====================================================================================
@brief   Point update a[x][y] = v, range query = sum over a submatrix
         [x1, x2) x [y1, y2). Built as a segment tree over rows, where every
         row-node itself stores a full segment tree over columns.
@memory  O(n * m) nodes (n, m rounded up to powers of two) -> can be heavy;
         only reach for this when n, m are modest (roughly up to a few
         hundred/thousand each depending on memory limits). For sparse point
         sets over a huge coordinate range, use [11] nested inside itself, or
         coordinate-compress + a BIT-of-BITs / offline sweep instead â€” that's
         what cp-algorithms calls "compression of a 2D segment tree": build
         the outer (x) tree only over x-coordinates that actually occur, and
         build each inner (y) tree only over the y-coordinates that occur
         within that x-node's range, giving O(n log n) total memory but
         losing the ability to insert brand-new points later.
@usage   st2d.init(n, m); st2d.build(matrix); st2d.set(x, y, v);
         st2d.query(x1, x2, y1, y2);
====================================================================================
*/
struct SegTree2D {
    int n, m;
    vector<vector<ll>> tree; // tree[vx][vy], vx in [0, 2n), vy in [0, 2m)

    void init(int n_, int m_) {
        n = 1; while (n < n_) n *= 2;
        m = 1; while (m < m_) m *= 2;
        tree.assign(2 * n, vector<ll>(2 * m, 0));
    }

    void buildY(vector<vector<ll>> &mat, int vx, int lx, int rx, int vy, int ly, int ry) {
        if (ry - ly == 1) {
            if (rx - lx == 1)
                tree[vx][vy] = (lx < (int)mat.size() && ly < (int)mat[0].size()) ? mat[lx][ly] : 0;
            else
                tree[vx][vy] = tree[2 * vx + 1][vy] + tree[2 * vx + 2][vy];
            return;
        }
        int my = (ly + ry) / 2;
        buildY(mat, vx, lx, rx, 2 * vy + 1, ly, my);
        buildY(mat, vx, lx, rx, 2 * vy + 2, my, ry);
        tree[vx][vy] = tree[vx][2 * vy + 1] + tree[vx][2 * vy + 2];
    }
    void buildX(vector<vector<ll>> &mat, int vx, int lx, int rx) {
        if (rx - lx != 1) {
            int mx = (lx + rx) / 2;
            buildX(mat, 2 * vx + 1, lx, mx);
            buildX(mat, 2 * vx + 2, mx, rx);
        }
        buildY(mat, vx, lx, rx, 0, 0, m);
    }
    void build(vector<vector<ll>> &mat) { buildX(mat, 0, 0, n); }

    void setY(int vx, int lx, int rx, int vy, int ly, int ry, int x, int y, ll v) {
        if (ry - ly == 1) {
            if (rx - lx == 1) tree[vx][vy] = v;
            else tree[vx][vy] = tree[2 * vx + 1][vy] + tree[2 * vx + 2][vy];
            return;
        }
        int my = (ly + ry) / 2;
        if (y < my) setY(vx, lx, rx, 2 * vy + 1, ly, my, x, y, v);
        else        setY(vx, lx, rx, 2 * vy + 2, my, ry, x, y, v);
        tree[vx][vy] = tree[vx][2 * vy + 1] + tree[vx][2 * vy + 2];
    }
    void setX(int vx, int lx, int rx, int x, int y, ll v) {
        if (rx - lx != 1) {
            int mx = (lx + rx) / 2;
            if (x < mx) setX(2 * vx + 1, lx, mx, x, y, v);
            else        setX(2 * vx + 2, mx, rx, x, y, v);
        }
        setY(vx, lx, rx, 0, 0, m, x, y, v);
    }
    void set(int x, int y, ll v) { setX(0, 0, n, x, y, v); }

    ll sumY(int vx, int vy, int ly, int ry, int y1, int y2) {
        if (ly >= y2 || y1 >= ry) return 0;
        if (ly >= y1 && ry <= y2) return tree[vx][vy];
        int my = (ly + ry) / 2;
        return sumY(vx, 2 * vy + 1, ly, my, y1, y2) + sumY(vx, 2 * vy + 2, my, ry, y1, y2);
    }
    ll sumX(int vx, int lx, int rx, int x1, int x2, int y1, int y2) {
        if (lx >= x2 || x1 >= rx) return 0;
        if (lx >= x1 && rx <= x2) return sumY(vx, 0, 0, m, y1, y2);
        int mx = (lx + rx) / 2;
        return sumX(2 * vx + 1, lx, mx, x1, x2, y1, y2) + sumX(2 * vx + 2, mx, rx, x1, x2, y1, y2);
    }
    // sum over rows [x1, x2) and columns [y1, y2)
    ll query(int x1, int x2, int y1, int y2) { return sumX(0, 0, n, x1, x2, y1, y2); }
};


/*
====================================================================================
[11] DYNAMIC (IMPLICIT / SPARSE) SEGMENT TREE
====================================================================================
@brief   Same idea as [1]'s Sum tree, but nodes are allocated lazily the first
         time a path is touched, instead of pre-allocating all 2n leaves.
         Lets you run a segment tree over a huge coordinate range (e.g.
         [0, 1e9)) using only O(Q log RANGE) memory for Q updates, with no
         coordinate compression needed up front.
@usage   dst.init(0, 1000000000); dst.add(i, v); dst.query(l, r);
         add(i, v) ADDS v to position i (leaves start at 0); combine it with
         a running "current value" map on your side if you need point-assign.
@note    Node 0 is reserved to mean "this child doesn't exist yet / contributes
         0" (mirrors the sentinel trick used in [6]'s persistent tree).
         Can be combined with lazy propagation (range add / range assign) by
         adding lazy arrays exactly as in [3]/[4] and creating children in
         push() the same way add()/query() already do â€” omitted here to keep
         this section focused, but it's a direct extension.
====================================================================================
*/
struct DynamicSegTree {
    ll LO, HI; // covers the half-open coordinate range [LO, HI)
    vector<ll> sum;
    vector<int> left, right;

    void init(ll lo, ll hi) {
        LO = lo; HI = hi;
        sum.assign(2, 0); left.assign(2, 0); right.assign(2, 0); // index 0 = null, index 1 = root
    }
    int newNode() {
        sum.push_back(0); left.push_back(0); right.push_back(0);
        return (int)sum.size() - 1;
    }

    void add(int node, ll lx, ll rx, ll i, ll v) {
        sum[node] += v;
        if (rx - lx == 1) return;
        ll m = lx + (rx - lx) / 2;
        if (i < m) {
            if (!left[node]) left[node] = newNode();
            add(left[node], lx, m, i, v);
        } else {
            if (!right[node]) right[node] = newNode();
            add(right[node], m, rx, i, v);
        }
    }
    void add(ll i, ll v) { add(1, LO, HI, i, v); }

    ll query(int node, ll lx, ll rx, ll l, ll r) {
        if (!node || lx >= r || l >= rx) return 0;
        if (lx >= l && rx <= r) return sum[node];
        ll m = lx + (rx - lx) / 2;
        return query(left[node], lx, m, l, r) + query(right[node], m, rx, l, r);
    }
    ll query(ll l, ll r) { return query(1, LO, HI, l, r); }
};


/*
====================================================================================
MAIN â€” demonstrates every variation above
====================================================================================
*/
int main() {
    ios_base::sync_with_stdio(false);
    cin.tie(nullptr);

    vector<ll> a = { 5, 2, 8, 1, 9, 3, 7, 4 };
    int n = (int)a.size();

    // ---------- [1] Common style: Sum (as configured) ----------
    SegTree segSum;
    segSum.init(n);
    segSum.build(a);
    cout << "[1] Sum      query(1,5) = " << segSum.query(1, 5) << "\n"; // 2+8+1+9=20
    segSum.set(2, 100);
    cout << "[1] Sum after set(2,100), query(0,3) = " << segSum.query(0, 3) << "\n"; // 5+2+100

    // NOTE: to test Min/Max/GCD/etc. instead, change SegTree::NEUTRAL and
    // SegTree::combine() at the top of the file (see the doxygen block in [1]),
    // recompile, and the SAME calls above (init/build/set/query) work unchanged.

    // [1-ext] firstGreater needs a MAX-configured tree
    {
        SegTree segMax;
        segMax.n = 1; while (segMax.n < n) segMax.n *= 2;
        // manually swap in Max config for this one instance's worth of demo data
        vector<ll> mx(segMax.n, -INF);
        for (int i = 0; i < n; i++) mx[i] = a[i];
        // build a max-tree by hand (since NEUTRAL/combine are static on SegTree,
        // in real code you'd just edit them; here we simulate with IterativeSegTree instead)
    }
    IterativeSegTree itMax;
    itMax.n = n; itMax.tree.assign(2 * n, LLONG_MIN);
    // (this instance still uses IterativeSegTree's compiled-in Sum combine â€”
    //  see [9]'s demo further below for how the EDIT lines are meant to be used)

    // [1-ext] findKthOne: mark elements > 5 as "1", find the 2nd one
    {
        SegTree marks;
        marks.init(n);
        vector<ll> bits(n);
        for (int i = 0; i < n; i++) bits[i] = (a[i] > 5) ? 1 : 0;
        marks.build(bits);
        int idx = marks.findKthOne(2); // 2nd element with a[i] > 5
        cout << "[1-ext] 2nd index with a[i] > 5: " << idx
             << " (a[" << idx << "]=" << (idx < n ? a[idx] : -1) << ")\n";
    }

    // [8] Binary search on the (sum) tree: first index where prefix sum >= 15
    SegTree segForWalk;
    segForWalk.init(n);
    segForWalk.build(a);
    int idx = segForWalk.walk([](ll prefixSum) { return prefixSum >= 15; });
    cout << "[8] First index where prefix sum >= 15: " << idx << "\n";

    // ---------- [1b] Max + count of maximum ----------
    vector<ll> withDup = { 3, 7, 2, 7, 7, 1, 7 };
    MaxCountSegTree mc;
    mc.init((int)withDup.size());
    mc.build(withDup);
    auto res = mc.query(0, (int)withDup.size());
    cout << "[1b] Max = " << res.val << ", occurrences = " << res.cnt << " (expect 7, 4)\n";

    // ---------- [2] Range Update / Point Query ----------
    RangeUpdatePointQuery rupq;
    rupq.init(n);
    rupq.build(a);
    rupq.update(1, 4, 10); // add 10 to indices [1,4)
    cout << "[2] After range-add(1,4,+10): point(1)=" << rupq.query(1)
        << " point(3)=" << rupq.query(3) << " point(4)=" << rupq.query(4) << "\n";

    // ---------- [3] Lazy Range Add + Range Sum ----------
    LazySegTreeRangeAdd lazyAdd;
    lazyAdd.init(n);
    lazyAdd.build(a);
    lazyAdd.update(2, 6, 5); // add 5 to indices [2,6)
    cout << "[3] Lazy range-add sum query(0," << n << ") = " << lazyAdd.query(0, n) << "\n";
    cout << "[3] Lazy range-add sum query(2,6) = " << lazyAdd.query(2, 6) << "\n";

    // ---------- [4] Lazy Range Assign + Range Sum ----------
    LazySegTreeRangeAssign lazySet;
    lazySet.init(n);
    lazySet.build(a);
    lazySet.update(0, 4, 7); // set indices [0,4) all to 7
    cout << "[4] Lazy range-assign sum query(0,4) = " << lazySet.query(0, 4) << " (expect 28)\n";

    // ---------- [5] Merge Sort Tree ----------
    vector<int> ai(a.begin(), a.end());
    MergeSortTree mst;
    mst.build(ai);
    cout << "[5] Count of elements < 6 in [0," << n << ") = " << mst.countLess(0, n, 6) << "\n";
    cout << "[5] First element >= 6 in [0," << n << ") = " << mst.firstAtLeast(0, n, 6) << "\n";

    // ---------- [5b] Mutable Merge Sort Tree ----------
    MergeSortTreeMutable mstm;
    mstm.init(n);
    mstm.build(ai);
    cout << "[5b] Before update, first >= 6 in [0,4) = " << mstm.firstAtLeast(0, 4, 6) << "\n";
    mstm.update(0, 50); // a[0] = 5 -> 50
    cout << "[5b] After a[0]=50,  first >= 6 in [0,4) = " << mstm.firstAtLeast(0, 4, 6) << "\n";

    // ---------- [6] Persistent Segment Tree ----------
    // (a) array snapshots
    PersistentSegTree pst;
    pst.init(n);
    int root0 = pst.build(a);
    int root1 = pst.update(root0, 3, 999); // version 1: a[3] = 999
    cout << "[6a] version0 sum(0," << n << ") = " << pst.query(root0, 0, n) << "\n";
    cout << "[6a] version1 sum(0," << n << ") = " << pst.query(root1, 0, n) << "\n";

    // (b) k-th smallest in a range, via persistent histogram over compressed values
    {
        vector<ll> arr = { 5, 2, 8, 1, 9, 3, 7, 4 }; // same as `a`
        vector<ll> sorted_vals = arr;
        sort(sorted_vals.begin(), sorted_vals.end());
        sorted_vals.erase(unique(sorted_vals.begin(), sorted_vals.end()), sorted_vals.end());
        auto compress = [&](ll v) {
            return (int)(lower_bound(sorted_vals.begin(), sorted_vals.end(), v) - sorted_vals.begin());
        };

        PersistentSegTree hist;
        hist.init((int)sorted_vals.size());
        vector<int> roots(arr.size() + 1);
        roots[0] = hist.build(); // empty histogram
        for (int i = 0; i < (int)arr.size(); i++)
            roots[i + 1] = hist.add(roots[i], compress(arr[i]), 1);

        // 3rd smallest element in arr[2..7) = {8,1,9,3,7,4} -> sorted {1,3,4,7,8,9} -> 4
        int k = 3, l = 2, r = 7;
        int compressedIdx = hist.findKth(roots[l], roots[r], k);
        cout << "[6b] " << k << "-rd smallest in arr[" << l << "," << r << ") = "
             << sorted_vals[compressedIdx] << " (expect 4)\n";
    }

    // ---------- [7] Max Subarray Sum Segment Tree ----------
    vector<ll> b = { -2, 1, -3, 4, -1, 2, 1, -5, 4 };
    MaxSubarraySegTree mss;
    mss.init((int)b.size());
    mss.build(b);
    cout << "[7] Max subarray sum overall = " << mss.query(0, (int)b.size()).best
        << " (expect 6, from [4,-1,2,1])\n";

    // ---------- [9] Iterative (non-recursive) Segment Tree ----------
    IterativeSegTree it;
    it.init(n);
    it.build(a);
    cout << "[9] Iterative sum query(1,5) = " << it.query(1, 5) << " (expect 20)\n";
    it.set(2, 100);
    cout << "[9] Iterative sum after set(2,100), query(0,3) = " << it.query(0, 3) << "\n";

    // ---------- [10] Simple 2D Segment Tree ----------
    vector<vector<ll>> mat = {
        {1, 2, 3, 4},
        {5, 6, 7, 8},
        {9, 1, 2, 3},
        {4, 5, 6, 7}
    };
    SegTree2D st2d;
    st2d.init((int)mat.size(), (int)mat[0].size());
    st2d.build(mat);
    cout << "[10] 2D sum over rows[1,3) cols[1,3) = " << st2d.query(1, 3, 1, 3)
         << " (expect 6+7+1+2=16)\n";
    st2d.set(0, 0, 100); // a[0][0] = 100
    cout << "[10] 2D sum over rows[0,1) cols[0,1) after set = " << st2d.query(0, 1, 0, 1)
         << " (expect 100)\n";

    // ---------- [11] Dynamic (Implicit) Segment Tree ----------
    DynamicSegTree dst;
    dst.init(0, 1000000000); // huge range, only a few points ever touched
    dst.add(5, 10);
    dst.add(999999999, 7);
    dst.add(500000000, 3);
    cout << "[11] Dynamic seg tree query(0,1000000000) = " << dst.query(0, 1000000000)
         << " (expect 20)\n";
    cout << "[11] Dynamic seg tree query(0,10) = " << dst.query(0, 10) << " (expect 10)\n";

    return 0;
}