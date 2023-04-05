import multiprocessing as mp
from multiprocessing import Manager
from multiprocessing.pool import Pool

from multiprocessing import Process
import os

class MyPool(Pool):
    def Process(self, *args, **kwds):
        proc = super(MyPool, self).Process(*args, **kwds)

        class NonDaemonProcess(proc.__class__):
            """Monkey-patch process to ensure it is never daemonized"""
            @property
            def daemon(self):
                return False

            @daemon.setter
            def daemon(self, val):
                pass

        proc.__class__ = NonDaemonProcess
        return proc


def get_Pool(cores):
    return Pool(cores)

def get_Manager():
    return Manager()

def get_cores():
    return mp.cpu_count()


def get_pid():
    return os.getpid()


def cores_left(process):
    num_cores = get_cores()

    pids = [int(x) for x in os.listdir('/proc') if x.isdigit()]

    num_children = 0
    for child_pid in pids:
        try:
            stat = open(f"/proc/{child_pid}/status", 'r')
            for line in stat:
                if line.startswith('PPid'):
                    ppid = int(line.split()[1])
                    break
            if ppid == process:
                num_children += 1

            stat.close()
        except FileNotFoundError:
            # Process may have terminated between the time of the process listing and now
            stat.close()
            pass

    active_processes = num_children + 1

    return num_cores - active_processes



class ListCallbackMultiProc:
    def __init__(self, list, lock):
        self._list = list
        self._lock = lock

    def __call__(self, cm, aut):
        with self._lock:
            self._list.append(cm.copy())

    def list(self):
        return self._list