
class ReachabilityOracle(object):
    """A reachability oracle with caching.
    TODO: move this part to a RMC lib.
    """

    def __init__(self, inits, posts, approx:int = None):
        """Inits = set of initial set of states (oracles),
           posts = set of post functions (oracles),
           """
        self._cache = {}
        self.inits = list(inits)
        self.posts = list(posts)
        self.approx = approx
        self._cache_tr = {}

    def _compute(self, n):
        """Compute the set of reachable states of size n. Simple BFS"""
        if n in self._cache:
            return
        visited = set()
        for r in range(1 if self.approx is None else (self.approx+1)):
            for init in self.inits:
                visited.update(init(n+r))
                if r>0 and n-r >= 0:
                    visited.update(init(n-r))
        todo = list(visited)
        while todo:
            src = todo.pop()
            if src not in self._cache_tr:
                self._cache_tr[src] = list()
                for post in self.posts:
                    for dst in post(src):
                        self._cache_tr[src].append(dst)
            for dst in self._cache_tr[src]:
                if dst in visited:
                    continue
                if self.approx is None:
                    assert(len(dst) == n)
                elif abs(len(dst) - n) > self.approx:
                    continue
                visited.add(dst)
                todo.append(dst)
            dst = None
        self._cache[n] = visited

    def query(self, w):
        n = len(w)
        self._compute(n)
        return w in self._cache[n]
