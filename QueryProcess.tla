------------------------------- MODULE QueryProcess -------------------------------
EXTENDS Integers, Sequences, rwLock
CONSTANT threadNum

SchemaCache_InsertDeleteLock == INSTANCE rwLock
SchemaCache_ReadWriteLock == INSTANCE rwLock
RegionWrite_ReadWriteLock == INSTANCE rwLock
DataRegion_InsertLock == INSTANCE rwLock

INIT == 
    /\ SchemaCache_InsertDeleteLock!Init 
    /\ SchemaCache_ReadWriteLock!Init
    /\ RegionWrite_ReadWriteLock!Init
    /\ DataRegion_InsertLock!Init

DeleteData ==
    /\ RegionWrite_ReadWriteLock!TryAcquireWLock
    /\ DataRegion_InsertLock!TryAcquireWLock
    /\ SchemaCache_ReadWriteLock!TryAcquireWLock
    /\ SchemaCache_ReadWriteLock!ReleaseWLock
    /\ DataRegion_InsertLock!ReleaseWLock
    /\ RegionWrite_ReadWriteLock!ReleaseWLock

InsertDataExecute == 
    /\ RegionWrite_ReadWriteLock!TryAcquireRLock
    /\ DataRegion_InsertLock!TryAcquireWLock
    /\ SchemaCache_ReadWriteLock!TryAcquireRLock
    \* update LastCache
    /\ SchemaCache_ReadWriteLock!ReleaseRLock
    /\ DataRegion_InsertLock!ReleaseWLock
    /\ RegionWrite_ReadWriteLock!ReleaseRLock

FetchRemoteSchema ==
    /\ SchemaCache_ReadWriteLock!TryAcquireRLock
    /\ threadNum > 0
    /\ threadNum' = threadNum - 1
    /\ SchemaCache_ReadWriteLock!ReleaseRLock

InsertData == 
    /\ DataRegion_InsertLock!TryAcquireWLock
    /\ SchemaCache_InsertDeleteLock!TryAcquireRLock
    /\ FetchRemoteSchema
    /\ InsertDataExecute
    /\ SchemaCache_InsertDeleteLock!ReleaseRLock
    /\ DataRegion_InsertLock!ReleaseWLock

DeleteTimseries_InvalidateCache ==
    /\ SchemaCache_InsertDeleteLock!TryAcquireWLock
    /\ SchemaCache_ReadWriteLock!TryAcquireWLock
    /\ SchemaCache_ReadWriteLock!ReleaseWLock
    /\ SchemaCache_InsertDeleteLock!ReleaseWLock

DeleteTimseries == 
    /\ DeleteTimseries_InvalidateCache
    /\ DeleteData

QueryData == 
    /\ threadNum > 0
    /\ threadNum' = threadNum - 1

NEXT == 
    \/ DeleteData
    \/ DeleteTimseries
    \/ InsertData
    \/ QueryData

SPACE ==
    INIT /\ [][NEXT]_<<>>

=============================================================================
