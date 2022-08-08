from typing import Dict, Generator, Mapping

import time
from contextlib import contextmanager

class Stopwatch:
    """
    A utility to collect time spent in multiple components

    Usage:
        stopwatch = Stopwatch()

        stopwatch.start("synthesis")
        # 3 seconds
        stopwatch.end("synthesis")
        
        stopwatch.start("completeness")
        # 2 seconds
        stopwatch.end("completeness")

        stopwatch.start("synthesis")
        # 1 seconds
        stopwatch.end("synthesis")
        
        # Now
        # stopwatch.get("synthesis") will be 3 + 1 = 4 seconds
        # stopwatch.get("completeness") will be 2 seconds
    """

    def __init__(self):
        # Total elapsed time of each component
        self.total_elapsed: Dict[str, float] = {}

        # Current start time of each component
        self.start_time: Dict[str, float] = {}

    def start(self, name: str) -> None:
        assert name not in self.start_time, f"starting component {name} multiple times"
        self.start_time[name] = time.time()

    def end(self, name: str) -> float:
        """
        Returns the time elapsed in the latest round
        """

        assert name in self.start_time, f"component {name} has not started"

        elapsed = time.time() - self.start_time[name]
        
        self.total_elapsed[name] = self.total_elapsed.get(name, 0.0) + elapsed
        del self.start_time[name]

        return elapsed

    @contextmanager
    def time(self, name: str) -> Generator[None, None, None]:
        try:
            self.start(name)
            yield
        finally:
            self.end(name)

    def get(self, name: str) -> float:
        """
        Get current elapsed time of a component (the timer could still be running)
        """

        base = self.total_elapsed.get(name, 0.0)

        if name in self.start_time:
            return time.time() - self.start_time[name] + base

        return base

    def get_all(self) -> Mapping[str, float]:
        return {
            name: self.get(name)
            for name in sorted(set(self.total_elapsed.keys()).union(set(self.start_time.keys())))
        }
