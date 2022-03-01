from typing import Iterable

from ..platforms.platform import SyscallNotImplemented, unimplemented
from .linux_syscalls import amd64

import logging

logger = logging.getLogger(__name__)


class SyscallStubs:
    """
    DEVELOPING NEW SYSTEM CALLS:
    * Whenever you need to add proper support for a system call to Manticore, cut and paste the stub from this file into
      manticore/platforms/linux.py.
    * The stubs include the correct names and number of parameters, but do not include type information
    * Filling out docstrings is left as an exercise for the reader.
    * If self.default_to_fail is set, the stubs will do whatever the syscall would do when an error occurs
        * Otherwise, they'll try to pretend that they succeeded.
    * If the stub doesn't know what behavior to produce, it'll raise a SyscallNotImplemented exception
        * Examples include: When a call doesn't just return -1 on failure or 0 on success
    """

    def __init__(self, *, default_to_fail=False, parent=None):
        self.default_to_fail = default_to_fail
        self.parent = parent

    def __getattr__(self, item):
        logger.warning(
            f"Getting {item!r} attribute from {self.__class__}: "
            "System calls should be copied and pasted into linux.py, "
            "not implemented within the stub file. "
            "If you're seeing this message, you may have forgotten to do that."
        )
        return getattr(self.parent, item)

    def simple_returns(self):
        return -1 if self.default_to_fail else 0

    def complicated_success(self, num):
        if self.default_to_fail:
            return -1
        else:
            raise SyscallNotImplemented(num, amd64[num])

    def complicated_error(self, num):
        if self.default_to_fail:
            raise SyscallNotImplemented(num, amd64[num])
        else:
            return 0

    def complicated_both(self, num):
        if self.default_to_fail:
            raise SyscallNotImplemented(num, amd64[num])
        else:
            raise SyscallNotImplemented(num, amd64[num])

    @unimplemented
    def sys_accept4(self, fd, upeer_sockaddr, upeer_addrlen, flags) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(288)

    @unimplemented
    def sys_add_key(self, _type, _description, _payload, plen) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(248)

    @unimplemented
    def sys_adjtimex(self, txc_p) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(159)

    @unimplemented
    def sys_alarm(self, seconds) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(37)

    @unimplemented
    def sys_bpf(self, cmd, attr, size) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(321)

    @unimplemented
    def sys_capget(self, header, dataptr) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_capset(self, header, data) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_clock_getres(self, which_clock, tp) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_clock_nanosleep(self, which_clock, flags, rqtp, rmtp) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_error(230)

    @unimplemented
    def sys_clock_settime(self, which_clock, tp) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_connect(self, fd, uservaddr, addrlen) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_creat(self, pathname, mode) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(85)

    @unimplemented
    def sys_delete_module(self, name_user, flags) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_dup3(self, oldfd, newfd, flags) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(292)

    @unimplemented
    def sys_eventfd(self, count) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(284)

    @unimplemented
    def sys_faccessat(self, dfd, filename, mode) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_fallocate(self, fd, mode, offset, len) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_fanotify_init(self, flags, event_f_flags) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(300)

    @unimplemented
    def sys_fanotify_mark(self, fanotify_fd, flags, mask, dfd, pathname) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_fchdir(self, fd) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_fchmod(self, fd, mode) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_fchmodat(self, dfd, filename, mode) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_fchown(self, fd, user, group) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_fchownat(self, dfd, filename, user, group, flag) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_fcntl(self, fd, cmd, arg) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(72)

    @unimplemented
    def sys_fdatasync(self, fd) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_fgetxattr(self, fd, name, value, size) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(193)

    @unimplemented
    def sys_finit_module(self, fd, uargs, flags) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_flistxattr(self, fd, list, size) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(196)

    @unimplemented
    def sys_flock(self, fd, cmd) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_fremovexattr(self, fd, name) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_fsetxattr(self, fd, name, value, size, flags) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_fstatfs(self, fd, buf) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_futimesat(self, dfd, filename, utimes) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_get_mempolicy(self, policy, nmask, maxnode, addr, flags) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_get_robust_list(self, pid, head_ptr, len_ptr) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_error(274)

    @unimplemented
    def sys_getcpu(self, cpup, nodep, unused) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_getdents64(self, fd, dirent, count) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(217)

    @unimplemented
    def sys_getgroups(self, gidsetsize, grouplist) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(115)

    @unimplemented
    def sys_getitimer(self, which, value) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_getpeername(self, fd, usockaddr, usockaddr_len) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_getpgid(self, pid) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(121)

    @unimplemented
    def sys_getpgrp(self) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(111)

    @unimplemented
    def sys_getppid(self) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(110)

    @unimplemented
    def sys_getpriority(self, which, who) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(140)

    @unimplemented
    def sys_getresgid(self, rgid, egid, sgid) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_getresuid(self, ruid, euid, suid) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_getrusage(self, who, ru) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_getsid(self, pid) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(124)

    @unimplemented
    def sys_getsockname(self, fd, usockaddr, usockaddr_len) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_getsockopt(self, fd, level, optname, optval, optlen) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_gettimeofday(self, tv, tz) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_getxattr(self, pathname, name, value, size) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(191)

    @unimplemented
    def sys_init_module(self, umod, len, uargs) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_inotify_add_watch(self, fd, pathname, mask) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(254)

    @unimplemented
    def sys_inotify_init(self) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(253)

    @unimplemented
    def sys_inotify_init1(self, flags) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(294)

    @unimplemented
    def sys_inotify_rm_watch(self, fd, wd) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_io_cancel(self, ctx_id, iocb, result) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_io_destroy(self, ctx) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_io_getevents(self, ctx_id, min_nr, nr, events) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(208)

    @unimplemented
    def sys_io_setup(self, nr_events, ctxp) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_io_submit(self, ctx_id, nr, iocbpp) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(209)

    @unimplemented
    def sys_ioperm(self, _from, num, turn_on) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_ioprio_get(self, which, who) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(252)

    @unimplemented
    def sys_ioprio_set(self, which, who, ioprio) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_kcmp(self, pid1, pid2, type, idx1, idx2) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(312)

    @unimplemented
    def sys_kexec_file_load(self, kernel_fd, initrd_fd, cmdline_len, cmdline_ptr, flags) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(320)

    @unimplemented
    def sys_kexec_load(self, entry, nr_segments, segments, flags) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(246)

    @unimplemented
    def sys_keyctl(self, option, arg2, arg3, arg4, arg5) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(250)

    @unimplemented
    def sys_lchown(self, filename, user, group) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_lgetxattr(self, pathname, name, value, size) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(192)

    @unimplemented
    def sys_linkat(self, oldfd, oldname, newfd, newname, flags) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_listxattr(self, pathname, list, size) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(194)

    @unimplemented
    def sys_llistxattr(self, pathname, list, size) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(195)

    @unimplemented
    def sys_lookup_dcookie(self, cookie64, buf, len) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(212)

    @unimplemented
    def sys_lremovexattr(self, pathname, name) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_lsetxattr(self, pathname, name, value, size, flags) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_mbind(self, start, len, mode, nmask, maxnode, flags) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_membarrier(self, cmd, flags) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(324)

    @unimplemented
    def sys_memfd_create(self, uname_ptr, flags) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(319)

    @unimplemented
    def sys_migrate_pages(self, pid, maxnode, old_nodes, new_nodes) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(256)

    @unimplemented
    def sys_mincore(self, start, len, vec) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_mknod(self, filename, mode, dev) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_mknodat(self, dfd, filename, mode, dev) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_mlock(self, start, len) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_mlock2(self, start, len, flags) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_mlockall(self, flags) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_modify_ldt(self, func, ptr, bytecount) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(154)

    @unimplemented
    def sys_mount(self, dev_name, dir_name, type, flags, data) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_move_pages(self, pid, nr_pages, pages, nodes, status, flags) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_mq_notify(self, mqdes, u_notification) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_mq_open(self, u_name, oflag, mode, u_attr) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(240)

    @unimplemented
    def sys_mq_timedreceive(self, mqdes, u_msg_ptr, msg_len, u_msg_prio, u_abs_timeout) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(243)

    @unimplemented
    def sys_mq_timedsend(self, mqdes, u_msg_ptr, msg_len, msg_prio, u_abs_timeout) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_mq_unlink(self, u_name) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_mremap(self, addr, old_len, new_len, flags, new_addr) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(25)

    @unimplemented
    def sys_msgctl(self, msqid, cmd, buf) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(71)

    @unimplemented
    def sys_msgget(self, key, msgflg) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(68)

    @unimplemented
    def sys_msgrcv(self, msqid, msgp, msgsz, msgtyp, msgflg) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(70)

    @unimplemented
    def sys_msgsnd(self, msqid, msgp, msgsz, msgflg) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_msync(self, start, len, flags) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_munlock(self, start, len) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_munlockall(self) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_name_to_handle_at(self, dfd, name, handle, mnt_id, flag) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_open_by_handle_at(self, dfd, name, handle, mnt_id, flags) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(304)

    @unimplemented
    def sys_pause(self) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return -1

    @unimplemented
    def sys_perf_event_open(self, attr_uptr, pid, cpu, group_fd, flags) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(298)

    @unimplemented
    def sys_personality(self, personality) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(135)

    @unimplemented
    def sys_pivot_root(self, new_root, put_old) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_poll(self, ufds, nfds, timeout_msecs) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(7)

    @unimplemented
    def sys_ppoll(self, ufds, nfds, tsp, sigmask, sigsetsize) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(271)

    @unimplemented
    def sys_prctl(self, option, arg2, arg3, arg4, arg5) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(157)

    @unimplemented
    def sys_preadv(self, fd, vec, vlen, pos_l, pos_h) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(295)

    @unimplemented
    def sys_process_vm_readv(self, pid, lvec, liovcnt, rvec, riovcnt, flags) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(310)

    @unimplemented
    def sys_process_vm_writev(self, pid, lvec, liovcnt, rvec, riovcnt, flags) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(311)

    @unimplemented
    def sys_ptrace(self, request, pid, addr, data) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(101)

    @unimplemented
    def sys_pwritev(self, fd, vec, vlen, pos_l, pos_h) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(296)

    @unimplemented
    def sys_quotactl(self, cmd, special, id, addr) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_readahead(self, fd, offset, count) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_readlinkat(self, dfd, pathname, buf, bufsiz) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(267)

    @unimplemented
    def sys_reboot(self, magic1, magic2, cmd, arg) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_recvfrom(self, fd, ubuf, size, flags, addr, addr_len) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(45)

    @unimplemented
    def sys_recvmmsg(self, fd, mmsg, vlen, flags, timeout) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(299)

    @unimplemented
    def sys_recvmsg(self, fd, msg, flags) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(47)

    @unimplemented
    def sys_remap_file_pages(self, start, size, prot, pgoff, flags) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_removexattr(self, pathname, name) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_renameat(self, oldfd, oldname, newfd, newname) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_renameat2(self, olddfd, oldname, newdfd, newname, flags) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_request_key(self, _type, _description, _callout_info, destringid) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(249)

    @unimplemented
    def sys_restart_syscall(self) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_both(219)

    @unimplemented
    def sys_rt_sigpending(self, set, sigsetsize) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_rt_sigqueueinfo(self, pid, sig, uinfo) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_rt_sigsuspend(self, unewset, sigsetsize) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_rt_sigtimedwait(self, uthese, uinfo, uts, sigsetsize) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(128)

    @unimplemented
    def sys_rt_tgsigqueueinfo(self, tgid, pid, sig, uinfo) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_sched_get_priority_max(self, policy) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(146)

    @unimplemented
    def sys_sched_get_priority_min(self, policy) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(147)

    @unimplemented
    def sys_sched_getaffinity(self, pid, len, user_mask_ptr) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_sched_getattr(self, pid, attr, size, flags) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_sched_getparam(self, pid, param) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_sched_getscheduler(self, pid) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(145)

    @unimplemented
    def sys_sched_rr_get_interval(self, pid, interval) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_sched_setaffinity(self, pid, len, user_mask_ptr) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_sched_setattr(self, pid, attr, flags) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_sched_setparam(self, pid, param) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_sched_setscheduler(self, pid, policy, param) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_sched_yield(self) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_seccomp(self, op, flags, uargs) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_select(self, n, inp, outp, fd_setexp, tvp) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(23)

    @unimplemented
    def sys_semctl(self, semid, semnum, cmd, arg) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(66)

    @unimplemented
    def sys_semget(self, key, nsems, semflg) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(64)

    @unimplemented
    def sys_semop(self, semid, tsops, nsops) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_semtimedop(self, semid, tsops, nsops, timeout) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_sendmmsg(self, fd, mmsg, vlen, flags) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(307)

    @unimplemented
    def sys_sendmsg(self, fd, msg, flags) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(46)

    @unimplemented
    def sys_sendto(self, fd, buff, len, flags, addr, addr_len) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(44)

    @unimplemented
    def sys_set_mempolicy(self, mode, nmask, maxnode) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_set_robust_list(self, head, len) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_error(273)

    @unimplemented
    def sys_setdomainname(self, name, len) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_setfsgid(self, gid) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_both(123)

    @unimplemented
    def sys_setfsuid(self, uid) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_both(122)

    @unimplemented
    def sys_setgid(self, gid) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_setgroups(self, gidsetsize, grouplist) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_sethostname(self, name, len) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_setitimer(self, which, value, ovalue) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_setns(self, fd, nstype) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_setpgid(self, pid, pgid) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_setpriority(self, which, who, niceval) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_setregid(self, rgid, egid) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_setresgid(self, rgid, egid, sgid) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_setresuid(self, ruid, euid, suid) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_setreuid(self, ruid, euid) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_setrlimit(self, resource, rlim) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_setsid(self) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(112)

    @unimplemented
    def sys_setsockopt(self, fd, level, optname, optval, optlen) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_settimeofday(self, tv, tz) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_setuid(self, uid) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_setxattr(self, pathname, name, value, size, flags) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_shmat(self, shmid, shmaddr, shmflg) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(30)

    @unimplemented
    def sys_shmctl(self, shmid, cmd, buf) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(31)

    @unimplemented
    def sys_shmdt(self, shmaddr) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_shmget(self, key, size, shmflg) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(29)

    @unimplemented
    def sys_shutdown(self, fd, how) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_sigaltstack(self, uss, uoss) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_signalfd(self, ufd, user_mask, sizemask) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(282)

    @unimplemented
    def sys_socketpair(self, family, type, protocol, usockvec) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_splice(self, fd_in, off_in, fd_out, off_out, len, flags) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(275)

    @unimplemented
    def sys_statfs(self, pathname, buf) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_swapoff(self, specialfile) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_swapon(self, specialfile, swap_flags) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_symlink(self, oldname, newname) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_symlinkat(self, oldname, newfd, newname) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_sync(self) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_sync_file_range(self, fd, offset, bytes, flags) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_syncfs(self, fd) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_sysfs(self, option, arg1, arg2) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(139)

    @unimplemented
    def sys_sysinfo(self, info) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_syslog(self, type, buf, len) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(103)

    @unimplemented
    def sys_tee(self, fdin, fdout, len, flags) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(276)

    @unimplemented
    def sys_tgkill(self, tgid, pid, sig) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_timer_create(self, which_clock, timer_event_spec, created_timer_id) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_timer_delete(self, timer_id) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_timer_getoverrun(self, timer_id) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(225)

    @unimplemented
    def sys_timer_gettime(self, timer_id, setting) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_timer_settime(self, timer_id, flags, new_setting, old_setting) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_timerfd_create(self, clockid, flags) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(283)

    @unimplemented
    def sys_timerfd_gettime(self, ufd, otmr) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_timerfd_settime(self, ufd, flags, utmr, otmr) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_times(self, info) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(100)

    @unimplemented
    def sys_tkill(self, pid, sig) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_truncate(self, path, length) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_unlinkat(self, dfd, pathname, flag) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_unshare(self, unshare_flags) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_ustat(self, dev, ubuf) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_utime(self, filename, times) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_utimensat(self, dfd, filename, utimes, flags) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_utimes(self, filename, utimes) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_vhangup(self) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @unimplemented
    def sys_vmsplice(self, fd, iov, nr_segs, flags) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(278)

    @unimplemented
    def sys_wait4(self, upid, stat_addr, options, ru) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.complicated_success(61)

    @unimplemented
    def sys_waitid(self, which, upid, infop, options, ru) -> int:
        """AUTOGENERATED UNIMPLEMENTED STUB"""
        return self.simple_returns()

    @staticmethod
    def unimplemented_syscalls() -> Iterable[str]:
        import inspect

        return (
            x[0].split("sys_", 1)[1]
            for x in inspect.getmembers(SyscallStubs, predicate=inspect.isfunction)
            if x[0].startswith("sys_")
        )

    @staticmethod
    def print_unimplemented_syscalls() -> None:
        for syscall in SyscallStubs.unimplemented_syscalls():
            print(syscall)
