#include "renamer.h"
#include <iostream>
#include <stdio.h>
#include <inttypes.h>
#include <cassert>
#include <cstdlib>

renamer :: renamer(uint64_t n_log_regs, uint64_t n_phys_regs, uint64_t n_branches, uint64_t n_active){
    

    assert(n_phys_regs > n_log_regs);
    assert((1 <= n_branches) && (n_branches <= 64));
    assert(n_active > 0);

    mappingTableSize = n_log_regs;
    freeListSize = n_phys_regs-n_log_regs;
    activeListSize = n_active;
    prfSize = n_phys_regs;
    numberOfBranches = n_branches;


    rmt.resize(mappingTableSize);
    amt.resize(mappingTableSize);
    
    auto it_rmt = rmt.begin();
    auto it_amt = amt.begin();
    uint64_t initValue = 0;
    
    for (; it_rmt != rmt.end() && it_amt != amt.end(); ++it_rmt, ++it_amt, ++initValue) {
        it_rmt->rmtMapping = initValue;
        it_amt->amtMapping = initValue;
    }

    
    fl.freeListMapping.resize(freeListSize); 
	fl.headIndex  = 0; 
    fl.tailIndex  = 0;
	fl.headPhase = 0; 
    fl.tailPhase = 1;

    auto it = fl.freeListMapping.begin();
    initValue = n_log_regs;
    
    for (; it != fl.freeListMapping.end(); ++it) {
        *it = initValue;
	++initValue;
    }
    

    

    al.activeListMapping.resize(activeListSize);

    al.headIndex  = 0; 
    al.tailIndex  = 0;
	al.headPhase = 0; 
    al.tailPhase = 0;

    for (auto it = al.activeListMapping.begin(); it != al.activeListMapping.end(); ++it) {
        it->destFlag = false;
        it->isComplete = false;
        it->exception = false;
        it->isLoadViolated = false;
        it->isValueMispredicted = false;
        it->isBranchMispredicted = false;
        it->isLoadInstr = false;
        it->isStoreInstr = false;
        it->isBranchInstr = false;
        it->isAtomicOper = false;
        it->isSysInstr = false;
        it->physicalRegIndex = 0;
        it->logicalRegIndex = 0;
        it->programCounter = 0;
    }
    

    
    prf.resize(prfSize);
    for (auto it = prf.begin(); it != prf.end(); ++it) {
        it->physRegReadyBit = true;
        it->phyRegisterValue = 0;
    }
    

    
    branchCheckpointTable.resize(numberOfBranches);
    for (auto it = branchCheckpointTable.begin(); it != branchCheckpointTable.end(); ++it) {
        it->shadowMapTable.resize(mappingTableSize);
    }
    
    GBM = 0;
}


bool renamer :: stall_reg(uint64_t bundle_dst){

    // Check how many free registers are available.
    // If number of free registers between tail and head  is less then bundle size, stall renaming as there are not enough physical
    // registers are available to rename consumers and producers of instructions.

    uint64_t retVal = 0;
    bool result = false;
    if (fl.headPhase==fl.tailPhase)
        retVal = (fl.tailIndex-fl.headIndex);
    else 
        retVal = (fl.tailIndex-fl.headIndex + freeListSize); 

    if (retVal< bundle_dst)
        result = true;
    else
        result = false; 

    
    return result;
}

bool renamer :: stall_branch(uint64_t bundle_branch){

    // Check if there are enough branch checkpoints available to rename all the branches in the bundle can be renmaed.
    uint64_t branchMask = 1;
    uint64_t availableCheckpoints = 0;
    for (uint64_t i=0; i<numberOfBranches; i++)
    {   
        // Go thtough the GBM bit by bit and check how many bits are 0(free and available for checkpointing).
        // If available Chcekpoints is greater than number of branch instructions available in the current bundle do not stall
        // else stall the renaming stage, because the branch instruction cannot be checkpointed.
        if(!(branchMask & GBM)) availableCheckpoints++;
        branchMask <<= 1; 
    }

    // Return true if available GBM bits to checkpoint is greater than number of branch instructions in the current bundle.
    return (availableCheckpoints < bundle_branch);
}

uint64_t renamer :: get_branch_mask(){
    // Return Global Branch Mask.
    return GBM;
    }

uint64_t renamer :: rename_rsrc(uint64_t log_reg){
    // Return renamed rmtMapping which has physical register index.
    return rmt[log_reg].rmtMapping;
    }

uint64_t renamer :: rename_rdst(uint64_t log_reg){
    //  Renaming the destination register.
    uint64_t retVal = fl.freeListMapping[fl.headIndex];

    // Rename the destination register by mapping it to the previous mapping.
    rmt[log_reg].rmtMapping = retVal;

    // After renaming increment the head Index of the free List.
    fl.headIndex++;

    // Check if the freeList is empty
    // If empty update headIndex and headPhase.
    if(fl.headIndex == freeListSize) { 
        fl.headIndex = 0; 
        fl.headPhase = !(fl.headPhase);
    }
    return retVal;
}

uint64_t renamer :: checkpoint(){

    // Creating a branch checkpoint
    uint64_t branchMask = 1;
    uint64_t branchIndex = 0;

    // Check the free Bit available in GBM to find the branch Mask and branch ID.
    while (branchMask & GBM) 
    {
        branchMask = branchMask <<  1; 
        branchIndex++;
    }

    // Update the GBM in order to checkpoint the branch instruction.
    GBM = GBM |  (1ULL << branchIndex);

    // Checkpoint the branch instruction by snap shoting current freeList head and phase bit
    // and the current GBM.
    branchCheckpointTable[branchIndex].checkPointedGBM = GBM;
    branchCheckpointTable[branchIndex].checkPointedFLHeadIndex = fl.headIndex;
    branchCheckpointTable[branchIndex].checkPointedFLHeadPhase = fl.headPhase;    

    // Update the shadow map table by copying the rmt to shadowm map table.
    auto it_shadow = branchCheckpointTable[branchIndex].shadowMapTable.begin();
    auto it_rmt = rmt.begin();
    
    for (; it_shadow != branchCheckpointTable[branchIndex].shadowMapTable.end() && it_rmt != rmt.end(); 
            ++it_shadow, ++it_rmt) {
        *it_shadow = it_rmt->rmtMapping;
    }
        

    // Return the branchIndex value.
    return branchIndex;
} 

bool renamer :: stall_dispatch(uint64_t bundle_inst){

    // Dispatching instructions has to be stalled if the active List doent have enough free entry to accomodate all the instructions in the 
    // bundle.

    // Check if hte active list is full by checking the phase bits,
    // If they are same there are some free entries, now check hwo many entries are available.
    uint64_t retVal = 0;
    if (al.headPhase==al.tailPhase)
        retVal = (activeListSize - (al.tailIndex - al.headIndex));
    else
        retVal = (al.headIndex - al.tailIndex);

    return (retVal< bundle_inst);
}

uint64_t renamer :: dispatch_inst(bool dest_valid, uint64_t log_reg, uint64_t phys_reg, bool load, bool store, bool branch, bool amo, bool csr, uint64_t programCounter){
    uint64_t retVal = 0;

    if(dest_valid)
    {
        al.activeListMapping[al.tailIndex].logicalRegIndex = log_reg; 
        al.activeListMapping[al.tailIndex].physicalRegIndex = phys_reg;
    }

    al.activeListMapping[al.tailIndex].isComplete               = false;      
    al.activeListMapping[al.tailIndex].isLoadViolated           = false;
    al.activeListMapping[al.tailIndex].exception                = false;      
    al.activeListMapping[al.tailIndex].isBranchMispredicted     = false;
    al.activeListMapping[al.tailIndex].isValueMispredicted      = false;  
    al.activeListMapping[al.tailIndex].destFlag                 = dest_valid; 
    al.activeListMapping[al.tailIndex].isLoadInstr              = load;
    al.activeListMapping[al.tailIndex].isStoreInstr             = store;      
    al.activeListMapping[al.tailIndex].isBranchInstr            = branch;
    al.activeListMapping[al.tailIndex].isAtomicOper             = amo;        
    al.activeListMapping[al.tailIndex].isSysInstr               = csr;    
    al.activeListMapping[al.tailIndex].programCounter           = programCounter;
    
    retVal = al.tailIndex;

    al.tailIndex++;

    if(al.tailIndex == activeListSize){
        al.tailIndex = 0; 
        al.tailPhase = !(al.tailPhase);
    }
    return retVal;
}

uint64_t renamer :: read(uint64_t phys_reg){
    return prf[phys_reg].phyRegisterValue;
    }
void renamer :: set_ready(uint64_t phys_reg){
    prf[phys_reg].physRegReadyBit = true;
    }
void renamer :: write(uint64_t phys_reg, uint64_t phyRegisterValue){
    prf[phys_reg].phyRegisterValue = phyRegisterValue;
    }
void renamer :: set_complete(uint64_t AL_index){
    al.activeListMapping[AL_index].isComplete = true;
    }
bool renamer :: is_ready(uint64_t phys_reg){
    return prf[phys_reg].physRegReadyBit;
    }
void renamer :: clear_ready(uint64_t phys_reg){
    prf[phys_reg].physRegReadyBit= false;
    }



void renamer :: resolve(uint64_t AL_index, uint64_t branch_ID, bool correct){
    if(correct)
    {   
        // When the branch is correctly predicted and it's GBM bit has to be
        // de-allocated and in all the other checkpointed bits of older instructions.

        // Free the bit allocated to the particular branch by resetting it to 0
        GBM =  GBM & ( ~(1ULL << branch_ID) );

        // Parse through all the checkpointed bits in the branchCheckPoint table and reset it to 0,
	// in order to free the GBM bit.
        for (auto it = branchCheckpointTable.begin(); it != branchCheckpointTable.end(); ++it) {
            it->checkPointedGBM = it->checkPointedGBM & (~(1ULL << branch_ID));
        }
           
    }
    else
    {
        // If the branch is mispredicted
        // Reset the mispredicted branch's checkpointed bit as this could be used by next instruction.
        branchCheckpointTable[branch_ID].checkPointedGBM &= (~(1ULL<<branch_ID));
        // Restore GBM
        GBM = branchCheckpointTable[branch_ID].checkPointedGBM;

        // Restore RMT of to the when it was during the particular branches checkpoint 
        auto it_rmt = rmt.begin();
        auto it_shadow = branchCheckpointTable[branch_ID].shadowMapTable.begin();
        
        for (; it_rmt != rmt.end() && it_shadow != branchCheckpointTable[branch_ID].shadowMapTable.end();
             ++it_rmt, ++it_shadow) {
            it_rmt->rmtMapping = *it_shadow;
        }
        

        // Restore free lsit headIndex and headPhase to what it was during checkpointing the branch.
        fl.headIndex  = branchCheckpointTable[branch_ID].checkPointedFLHeadIndex;
        fl.headPhase = branchCheckpointTable[branch_ID].checkPointedFLHeadPhase;
        // Increment the tailIndex 
        al.tailIndex  = AL_index + 1;

        // Check if the activelist is full
        if(al.tailIndex == activeListSize) al.tailIndex = 0;


        if(al.headIndex < al.tailIndex)
            al.tailPhase = al.headPhase;
        else 
            al.tailPhase =!al.headPhase;
    }
} 

bool renamer :: precommit(bool &completed, bool &exception, bool &load_viol, bool &br_misp, bool &val_misp, bool &load, bool &store, bool &branch, bool &amo, bool &csr, uint64_t &programCounter){
    // Fucntion to examine the instruction at the head of the active list.
    if((al.headIndex == al.tailIndex) && (al.headPhase == al.tailPhase)) {
	    return false;
    		// return false as the active list is empty.
    } else{
	    
    branch    = al.activeListMapping[al.headIndex].isBranchInstr;
    amo       = al.activeListMapping[al.headIndex].isAtomicOper;     
    csr       = al.activeListMapping[al.headIndex].isSysInstr;
    completed = al.activeListMapping[al.headIndex].isComplete;    
    load_viol = al.activeListMapping[al.headIndex].isLoadViolated;       
    br_misp   = al.activeListMapping[al.headIndex].isBranchMispredicted;
    val_misp  = al.activeListMapping[al.headIndex].isValueMispredicted;      
    load      = al.activeListMapping[al.headIndex].isLoadInstr;
    programCounter        = al.activeListMapping[al.headIndex].programCounter; 
    store     = al.activeListMapping[al.headIndex].isStoreInstr;   
 
    exception = al.activeListMapping[al.headIndex].exception;

    return true;
    }
}

void renamer :: commit(){
    assert(al.activeListMapping[al.headIndex].isComplete == true);
    assert(al.activeListMapping[al.headIndex].exception== false);
    assert(al.activeListMapping[al.headIndex].isLoadViolated == false);

    // Check validity of the destination register readiness.
    if (al.activeListMapping[al.headIndex].destFlag == true)
    {
        // Freeing the phyical register that was present at AMT i.e.//
        // the phys reg that logical register is mapping to is entered into the free List.
        fl.freeListMapping[fl.tailIndex] = amt[al.activeListMapping[al.headIndex].logicalRegIndex].amtMapping;
        // increment the tailIndex.
        fl.tailIndex++;

        // If the free list is equal to freelistsize reset tailindex and phase bit.
        if(fl.tailIndex == freeListSize){ 
            fl.tailIndex = 0; 
            fl.tailPhase = !(fl.tailPhase);
        }

        // 
        amt[al.activeListMapping[al.headIndex].logicalRegIndex].amtMapping= al.activeListMapping[al.headIndex].physicalRegIndex;
    }
    al.headIndex++;

    // Check if the activeList is full
    if(al.headIndex == activeListSize){
        al.headIndex=0; 
        al.headPhase=!al.headPhase;}
}

void renamer :: squash()
{
    // Squasing all the instructions in the pipeline, activelist and free list.
    al.tailIndex = al.headIndex; 
    al.tailPhase = al.headPhase; 
    fl.headIndex = fl.tailIndex; 
    fl.headPhase = !fl.tailPhase; 

    // As AMT has the commited state,
    // copy AMT to RMT
    auto it_rmt = rmt.begin();
    auto it_amt = amt.begin();
    
    for (; it_rmt != rmt.end() && it_amt != amt.end(); ++it_rmt, ++it_amt) {
        it_rmt->rmtMapping = it_amt->amtMapping;
    }

    // Set Physical Register bit 
    for (auto it = prf.begin(); it != prf.end(); ++it) {
        it->physRegReadyBit = true;
    }
    

    // Now the checkpointed values are of nwo use because of misprediction thus reset them.
    for (auto& checkpoint : branchCheckpointTable) {
        // Reset the shadowMapTable for each checkpoint
        std::fill(checkpoint.shadowMapTable.begin(), checkpoint.shadowMapTable.end(), 0);
        checkpoint.checkPointedFLHeadIndex = 0;
        checkpoint.checkPointedFLHeadPhase = 0;
        checkpoint.checkPointedGBM = 0;
    }
    
    GBM = 0;
}

void renamer :: set_load_violation(uint64_t AL_index){
    al.activeListMapping[AL_index].isLoadViolated = true;
    }
void renamer :: set_branch_misprediction(uint64_t AL_index){
    al.activeListMapping[AL_index].isBranchMispredicted = true;
    }
void renamer :: set_exception(uint64_t AL_index){
    al.activeListMapping[AL_index].exception = true;
    }

void renamer :: set_value_misprediction(uint64_t AL_index){
    al.activeListMapping[AL_index].isValueMispredicted = true;
    }
bool renamer :: get_exception(uint64_t AL_index){
    return al.activeListMapping[AL_index].exception;
    }