
    def write(self, reg, value):
        from binaryninja.enums import ImplicitRegisterExtend

        r = self._alias(str(reg))
        # if this is a custom register just write to the dictionary
        if r not in self.view.arch.regs:
            self.registers[r] = value
            return

        # get the ILRegister object from Architecture
        ilreg = self.view.arch.regs[r]

        # full_width -> just write to it
        if ilreg.full_width_reg == r:
            self.registers[r] = value
            return

        ilreg_full = self.view.arch.regs[ilreg.full_width_reg]
        full_width_reg_value = self.registers[ilreg.full_width_reg]
        if ilreg.extend == ImplicitRegisterExtend.NoExtend:
            # mask off the value that will be replaced
            mask = (1 << ilreg.size * 8) - 1
            full_mask = (1 << ilreg_full.size * 8) - 1
            reg_bits = mask << (ilreg.offset * 8)
            full_width_reg_value &= full_mask ^ reg_bits
            full_width_reg_value |= value << ilreg.offset * 8
        elif ilreg.extend == ImplicitRegisterExtend.ZeroExtendToFullWidth:
            full_width_reg_value = value
        elif ilreg.extend == ImplicitRegisterExtend.SignExtendToFullWidth:
            full_width_reg_value = (
                (value ^ ((1 << ilreg.size * 8) - 1)) -
                ((1 << ilreg.size * 8) - 1) +
                (1 << ilreg_full.size * 8)
            )
        else:
            raise NotImplementedError

        self.registers[ilreg.full_width_reg] = full_width_reg_value

    def read(self, reg):
        r = self._alias(str(reg))
        if r in self.registers:
            return self.registers[r]

        reg_info = self.view.arch.regs[r]
        full_reg_value = self.registers[reg_info.full_width_reg]
        mask = (1 << reg_info.size * 8) - 1
        reg_bits = mask << (reg_info.offset * 8)
        reg_value = (full_reg_value & reg_bits) >> (reg_info.offset * 8)
        return reg_value
