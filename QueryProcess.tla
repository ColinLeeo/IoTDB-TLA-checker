------------------------------- MODULE QueryProcess -------------------------------
EXTENDS Integers, Sequences, rwLock
CONSTANT threadNum

INSTANCE SchemaCache_InsertDeleteLock == INSTANCE rwlock
INSTANCE SchemaCache_ReadWriteLock == INSTANCE rwlock
INSTANCE RegionWrite_ReadWriteLock == INSTANCE rwlock
INSTANCE DataRegion_InsertLock == INSTANCE rwlock

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
    /\ Dataregion_InsertLock!ReleaseWLock



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
    INIT /\ [][NEXT]_<<
    SchemaCache_InsertDeleteLock!readers, 
    SchemaCache_InsertDeleteLock!waitingWriters, 
    SchemaCache_InsertDeleteLock!writer, 
    SchemaCache_InsertDeleteLock!queue,
    SchemaCache_ReadWriteLock!readers, 
    SchemaCache_ReadWriteLock!waitingWriters, 
    SchemaCache_ReadWriteLock!writer, 
    SchemaCache_ReadWriteLock!queue,
    RegionWrite_ReadWriteLock!readers, 
    RegionWrite_ReadWriteLock!waitingWriters, 
    RegionWrite_ReadWriteLock!writer, 
    RegionWrite_ReadWriteLock!queue,
    DataRegion_InsertLock!readers, 
    DataRegion_InsertLock!waitingWriters, 
    DataRegion_InsertLock!writer, 
    DataRegion_InsertLock!queue,>>
    


