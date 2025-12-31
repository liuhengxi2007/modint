import gdb

class MintPrinter:
	def __init__(self, val):
		self.val = val
		self.MOD = int(gdb.parse_and_eval("MOD"))
	def to_string(self):
		if 'mint_acc' in str(self.val.type):
			value = int(self.val['a0']) + int(self.val['a1']) * 2**64
		else:
			value = int(self.val['a'])
		return str(value % self.MOD)

def mint_printer_lookup(val):
	type_name = str(val.type)
	if 'modint::mint' in type_name or 'modint::mint' in type_name:
		return MintPrinter(val)
	return None

gdb.pretty_printers.append(mint_printer_lookup)
