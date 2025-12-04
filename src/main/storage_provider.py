from storage_disk import DiskReplicaBackend
from storage_memory import MemoryReplicaBackend

BACKEND = DiskReplicaBackend()
BACKEND_TYPE = "disk"

def use_disk_backend():
    global BACKEND
    BACKEND = DiskReplicaBackend()
    global BACKEND_TYPE
    BACKEND_TYPE = "disk"

def use_memory_backend():
    global BACKEND
    BACKEND = MemoryReplicaBackend()
    global BACKEND_TYPE
    BACKEND_TYPE = "memory"

def get_backend():
    return BACKEND

def get_backend_type():
    return BACKEND_TYPE
