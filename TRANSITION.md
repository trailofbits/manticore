# Big Bad Manticore/Unicorn Transition Doc
It looks like we'll be shelving the Manticore's Unicorn-backed concrete mode (Manticorn?) for a while in favor of more pressing features. This document will serve as a record of all the issues and to-dos from this branch so that we can revive it more easily in the future. 

### Original goals
Create a fast, purely-concrete execution mode with analyis for Manticore. The idea was to replace Pin in Sienna Locomotive with an in-house tool that was easier to use than Pin, but faster than Manticore. We decided that the best way to do this was to use Unicorn's fast qemu-based CPU emulation as a replacement for Manticore's relatively slow python-based instruction emulation. 

### Structure 
On `master`, whenever an `abstractcpu` can't find an implementation for an instruction, it spins up a Unicorn instance, executes the instruction, and replicates any reads to Unicorn's memory or registers into Manticore's cpu. This branch modifies `abstractcpu` to instead send every instruction to the Unicorn instance (and preserve the instance across instructions). In order to make this more efficient, we try to let Unicorn run independently from Manticore as much as possible. When we initialize the emulator, we clone Manticore's image of the program memory into Unicorn, then tell Unicorn to execute each instruction in the text segment based on wherever Manticore thinks the program counter is pointing. With the exception of the program counter, we don't sync changes to the memory or the registers back to Manticore after every instruction, instead choosing to do it lazily whenever we need to hand control back to Manticore. Currently, that only happens whenever we need to execute a syscall, since Unicorn can't emulate those. When that happens, we sync Unicorn's state to Manticore's, then invoke Manticore's syscall emulation, and write any changes to the memory or registers back into the Unicorn instance. We implement the write-back by subscribing callbacks in the emulator to the `did_write_memory` and `did_set_register` events.

### Issues
* The sync-up from Unicorn to Manticore that occurs immediately before a syscall should probably occur any time Manticore hits a hook as well, but that's currently not implemented. 
* The taint-tracking system doesn't work yet with this branch, since the emulator makes no effort to track it.
* Manticore's default way of implementing file reads seems to be creating a symbolic file, and treating anything read from it as symbolic input. This doesn't make a lot of sense for a pure concrete mode - when a binary wants to read flag.txt, we should just let it read flag.txt. Implementing this will mean modifying all the syscalls that read from symbolic files to add a check for whether we're executing on the Unicorn emulator, in which case, they should read from the actual filesystem.
    * For example, in `multiple-styles`,  we get the read from stdin to work by shoving some bytes at the binary via `concrete_start`. If we don't do this, it reads symbolic memory, which gets concretized to null bytes. This is probably not the ideal behavior. While we still want concrete initialization data to work, It would make more sense for this to read from stdin like a real binary would. 
* The initial write to the `DS` register causes Unicorn to segfault when running CGC binaries. No idea why this is happening. Currently, the segmentation code only handles FS (and relies on some Unicorn fakery, not a real GDT), so it's possible that fixing this would make the segfault go away.
* It takes an extremely long time to clone Manticore's memory image into Unicorn. This is almost entirely because Manticore implements memory using a dict, and we can't just take a big slice of the dict nearly as efficiently as we can do so with a list. Options for fixing this include creating a flat copy of the program memory within Manticore during initialization, or writing/finding a separate loader just for Unicorn.
* Performance analysis of the in-step time (the total time spent waiting for Unicorn to execute instructions) and the out-of-step time (Out of step time = <Total time> - <Time to initialize Manticore and Unicorn> - <In step time>) has revealed that most of the time spent executing a program is initialization time and out-of-step time. While it's still important to minimize the in-step time (Say, by chunking instructions into blocks that Unicorn can run without handing control back to the abstractcpu), we could probably see more immediate gains by working to minimize the out-of-step time. 
* While we shouldn't have to worry about symbolic data in a mode designed for purely-concrete execution, the current implementation doesn't always handle it well. Ideally, we should concretize any memory or registers to a single value before handing them off to Unicorn, but that seems to be a bit buggy. 
    *  In the distant future, we could think about concretizing to multiple values, spinning up Unicorn instances for each possibilty, and merging the changes from each instance back into their respective states. This is, for now, a bit too ambitious. 

### To-do's (before transition)
*   [x] Modularize unicorn backend and add API flag so that we can switch to it without breaking normal Manticore features when it's off
*   [x] Strip out extraneous debugging information
*   [x] Clean up timing code (left in for future usage) 
*   [x] Document *all* the things (including expanding this document)
*   [x] Merge current master back into dev branch

### To-do's (long term)
* Decrease out-of-step and initialization time so that we can regularly beat stock Manticore
* Fix CGC segfault
* Fix file reads and writes
* Implement taint tracking
* Write unit tests and a framework for comparing Manticore's state after emulating a program via Unicorn and its state after emulating a program internally.
