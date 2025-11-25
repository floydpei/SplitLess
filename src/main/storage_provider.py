from storage_disk import DiskReplicaBackend
from storage_memory import MemoryReplicaBackend

BACKEND = DiskReplicaBackend()

def use_disk_backend():
    global BACKEND
    BACKEND = DiskReplicaBackend()

def use_memory_backend():
    global BACKEND
    BACKEND = MemoryReplicaBackend()

def get_backend():
    return BACKEND
