# coding: utf-8
# this module contains the computation of what node is not needed
from queue import Queue


class GraphReach:
    def __init__(self, nodes, use_map, concrete_vals):
        """
        nodes : set/list of width/nodes
        use_map : node -> [list of width it uses], no need to have self-loop, should be okay
        concrete_vals : set/list of width/nodes that can start from
        """
        self.nodes = nodes
        self.to_map = {}
        self.start = concrete_vals

        for dst, srcs in use_map.items():
            for src in srcs:
                if src not in self.to_map:
                    self.to_map[src] = set([])
                self.to_map[src].add(dst)

    def compute_reach(self):
        reachable_set = set([])
        q = Queue()

        for v in self.start:
            reachable_set.add(v)
            q.put(v)

        while not q.empty():
            v = q.get()
            for dst in self.to_map.get(v, []):
                if dst not in reachable_set:
                    reachable_set.add(dst)
                    q.put(dst)

        return reachable_set


if __name__ == '__main__':
    g = GraphReach([0, 1, 2, 4], {0: [1, 2], 1: [0], 4: [0, 1]}, [1])
    print(g.compute_reach())
