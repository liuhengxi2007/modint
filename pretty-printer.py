import gdb

class MintPrinter:
	def __init__(self, val):
		self.val = val
		self.MOD = int(gdb.parse_and_eval("MOD"))
		self.THRES = 4001
	def to_string(self):
		if 'mint_acc' in str(self.val.type):
			value = int(self.val['a0']) + int(self.val['a1']) * 2**64
		else:
			value = int(self.val['a'])
		value %= self.MOD
		format_spec = chr(gdb.convenience_variable('mf'))
		if format_spec == "d":
			value -= (2 * value >= self.MOD) * self.MOD
		elif format_spec == "f":
			best = (value + 1, value, 1)
			for i in range(1, self.THRES):
				num = value * i % self.MOD
				best = min(best, (num + i, num, i))
				num = value * -i % self.MOD
				best = min(best, (num + i, -num, i))
			value = str(best[1]) + ('/' + str(best[2]) if best[2] != 1 else '')
		return str(value)

def mint_printer_lookup(val):
	type_name = str(val.type)
	if type_name.startswith('modint::mint'):
		return MintPrinter(val)
	return None

gdb.pretty_printers.append(mint_printer_lookup)

"""
~/.gdbinit
source /path/to/pretty-printer.py
alias mfu=set $mf='u'
alias mfd=set $mf='d'
alias mff=set $mf='f'
mfu
"""
