# Utilities for representing partitions - Young Diagrams and maybe I'll do the abacus notation (abacuses? abaci?) as well.

import weakref

def mod(value, modulus):
	"""
	The % operation does not allow modulus by zero. Mathematically, this should correspond to taking Z/0Z, i.e., just Z. Since there's no
	division by zero involved, python does % wrong.
	"""
	if modulus != 0: return value % modulus
	else: return value

class Partition(object):
	"""
	Represents a partition as a non-increasing tuple of positive integers.
	"""
	_cache = weakref.WeakValueDictionary()
	def __new__(cls, parts):
		if parts in cls._cache:
			return cls._cache[parts]
		# parts should be a decreasing tuple of positive integers.
		assert isinstance(parts, tuple)
		assert all(isinstance(i, int) for i in parts)
		assert all((i > 0) for i in parts)
		assert all((parts[i]>=parts[i+1]) for i in range(len(parts)-1))
		self = object.__new__(cls)
		self.parts = parts
		cls._cache[parts] = self
		return self
	def __hash__(self): return hash(self.parts)
	def __eq__(self, other): return self.parts == other.parts
	def __repr__(self): return "Partition(%r)"%(self.parts,)
	def __str__(self): return self.young_diagram_string()
	def __lt__(self, other): return self.parts < other.parts
	def young_diagram_list(self):
		"""
		Returns a list of list of points in the plane corresponding to the (French) Young Diagram.
		"""
		return [ [(i, j) for i in range(self.parts[j])]
			for j in range(len(self.parts))]
	def young_diagram_set(self):
		"""
		Returns a set of points in the plane corresponding to the (French) Young Diagram.
		"""
		return set((i, j) for j in range(len(self.parts)) for i in range(self.parts[j]))
	def young_diagram_iter(self):
		for j in range(len(self.parts)):
			for i in range(self.parts[j]):
				yield (i, j)
	def young_diagram_string(self):
		"""
		Returns a string representing the Young Diagram graphically (top-heavy - English notation).
		"""
		return "\n".join("*"*i for i in self.parts)
	def content(self):
		cont = {}
		for (i, j) in self.young_diagram_iter():
			cont[i-j] = cont.get(i-j, 0)+1
		return cont
	def modular_content(self, modulus):
		e = modulus
		cont = {}
		for (i, j) in self.young_diagram_iter():
			residue = mod((i-j), e) # Apparently python3 puts the modulus between 0 and e-1, so that's convenient.
			cont[residue] = cont.get(residue, 0)+1
		return cont
	def content_defects(self, modulus):
		e = modulus
		content = self.modular_content(e)
		return tuple(content[(i-1)%e]-content[i] for i in range(e))
	def abacus(self):
		"""
		Returns a list of beads on the abacus, indexed by integers. The smallest bead is the last bead before the displaced ones, and the largest bead is the last bead.
		"""
		li = [self.parts[i]-i for i in range(len(self.parts))]
		li.append(-len(self.parts))
		li.reverse()
		return li
	def abacus_string(self):
		"""
		Returns a string with * for each bead and - for each space that has no bead.
		"""
		abacus = self.abacus()
		lower = abacus[0]
		upper = abacus[-1]+1
		li = [("-", "*")[i in abacus] for i in range(lower, upper)]
		return "".join(li)
	def total(self):
		"""
		Given p a Partition of n, p.total() returns n.
		"""
		return sum(self.parts)
	# The following 4 functions are (normal & modular) restriction and induction generators; they are all computed using abacus
	# notation, because adding an i-cell corresponds to moving a bead from i to i+1, and removing an i-cell corresponds to
	# moving a bead from i+1 to i.
	def induct(self, index):
		"""
		Generator (of length at most one) for the partition obtained by adding a cell with content given by index.
		"""
		abacus = self.abacus()
		abacus.insert(0, abacus[0]-1) # Needed for adjusting the first bead.
		try:
			list_index = abacus.index(index)
			if list_index+1 == len(abacus):
				# Last bead. Move it up.
				abacus[list_index] += 1
			elif abacus[list_index+1]>index+1:
				# We've checked that the coast is clear. Move the bead up.
				abacus[list_index] += 1
			else:
				# There is no addable node. Go away.
				return
			yield partition_from_abacus(abacus)
		except(ValueError):
			return # Or pass, or whatever, man.
	def restrict(self, index):
		"""
		Generator (of length at most one) for the partition obtained by removing a cell with content given by index.
		"""
		abacus = self.abacus()
		try:
			list_index = abacus.index(index+1)
			if list_index == 0:
				# First bead. Cannot move it down. Go away.
				return
			elif abacus[list_index-1]<index:
				# We've checked that the coast is clear. Move the bead down.
				abacus[list_index] -= 1
			else:
				# There is no removable node. Go away.
				return
			yield partition_from_abacus(abacus)
		except(ValueError):
			return # Or pass, or whatever, man.
	# For the modular case, it seems, at least naively, that the most efficient way to traverse the partitions
	# is to loop through the abacus directly, skipping over the irrelevant beads.
	# I suppose the next step to optimize would be to introduce a binary search for each relevant index, but
	# that's probably not worth it.
	def modular_induct(self, modulus, index):
		"""
		Generator for partitions obtained by adding a cell with modular content given by index.
		"""
		abacus = self.abacus()
		abacus.insert(0, abacus[0]-1) # Needed for adjusting the first bead.
		# This for loop modifies elements of the list already seen, not future elements, so it's okay.
		for (list_index, bead_position) in enumerate(abacus):
			if (mod(bead_position, modulus)) == index:
				# Need to check whether we can move this bead up.
				if (list_index+1 == len(abacus)) or (abacus[list_index+1]>bead_position+1):
					# Now we move the bead, yield the corresponding partition,
					# then return the bead to its original position.
					abacus[list_index] += 1
					yield partition_from_abacus(abacus)
					abacus[list_index] -= 1
	def modular_restrict(self, modulus, index):
		"""
		Generator for partitions obtained by adding a cell with modular content given by index.
		"""
		abacus = self.abacus()
		# This for loop modifies elements of the list already seen, not future elements, so it's okay.
		for (list_index, bead_position) in enumerate(abacus):
			if (mod((bead_position-1), modulus)) == index:
				# Need to check whether we can move this bead down.
				if (list_index > 0) and (abacus[list_index-1]<bead_position-1):
					# Now we move the bead, yield the corresponding partition,
					# then return the bead to its original position.
					abacus[list_index] -= 1
					yield partition_from_abacus(abacus)
					abacus[list_index] += 1
	def delta(self):
		"""
		Returns the LinearCombinationOfPartitions object consisting of the given partition alone.
		"""
		return LinearCombinationOfPartitions({self : 1})
	def crystal_induct(self, modulus, index):
		"""
		Computes the next larger partition in the Crystal graph along the given index, as described in Chapter 11 of Kleschev's book.

		If there is no partition with the given index, returns None.
		"""
		# In terms of the abacus, an i-addable node corresponds to a bead on position i with position i+1 cleared,
		# and an i-removable node corresponds to a bead on position i+1 with position i cleared.

		# To record either kind of node, we record the position of the corresponding bead. This means:
		# To record an i-addable node, we record the absolute index corresponding to i (i.e., not taken modulo the modulus).
		# To record an i-removable node, we record the absolute index corresponding to i+1.
		i = index
		i_plus_1 = (index+1)%modulus
		abacus = self.abacus()
		i_signature = []
		for (list_index, absolute_index) in enumerate(abacus):
			if (((absolute_index % modulus) == i) and
			 (list_index + 1 == len(abacus) or abacus[list_index+1]>absolute_index+1)):
				# i-addable node
				i_signature.append(absolute_index)
			if (((absolute_index % modulus) == i_plus_1) and
			 (list_index > 0 and abacus[list_index-1]<absolute_index-1)):
				# i-removable node
				i_signature.append(absolute_index)
		# Now we reduce the i-signature.
		list_index = 0
		while 0 < list_index + 1 < len(i_signature):
			if (i_signature[list_index]%modulus == i_plus_1) and (i_signature[list_index+1]%modulus == i):
				del i_signature[list_index]
				del i_signature[list_index]
				if list_index > 0:
					list_index -= 1
			else:
				list_index += 1
		# Find the last + in the reduced i-signature.
		if len(i_signature) == 0 or i_signature[0]%modulus != i: return None
		list_index = 0
		while list_index < len(i_signature) and i_signature[list_index]%modulus == i:
			list_index += 1
		gen = self.induct(i_signature[list_index-1])
		for p in gen:
			return p

def partition_from_abacus(abacus):
	"""
	Constructs a Partition object given partition.abacus().

	Note that it is assumed that the abacus is centered at 0. Extra beads in the front are allowed.
	"""
	parts = []
	for i in range(len(abacus)-1):
		next_part = abacus[-i-1]+i
		if next_part>0:
			parts.append(next_part)
		else:
			break
	return Partition(tuple(parts))

def string_from_abacus(abacus):
	"""
	Returns a string with * for each bead and - for each space that has no bead.
	"""
	lower = abacus[0]
	upper = abacus[-1]+1
	li = [("-", "*")[i in abacus] for i in range(lower, upper)]
	return "".join(li)

def abacus_from_content_defects(modulus, defects):
	"""
	Constructs the abacus corresponding to an e-core Partition object with the given defects. Note that the defects must add up to 0.
	"""
	# TODO is e=0 allowed?
	e = modulus
	# We compute the abacus. First we use the defects to compute the sub-abacuses given by skipping every e-th position.
	# Each sub-abacus is just the standard (empty partition) abacus shifted by the defect, so it's determined by its last bead.
	neutral_positions = tuple((i-e) if i>0 else i for i in range(e))
	last_beads = tuple(defects[i]*e+neutral_positions[i] for i in range(e))
	last_bead_before_displaced = min(last_beads)
	last_bead = max(last_beads)
	abacus = []
	for i in range(last_bead_before_displaced, last_bead+1):
		if i<=last_beads[i%e]:
			abacus.append(i)
	# Now it is possible the abacus has more beads in front than necessary. This is okay; the partition_from_abacus() function is trained to handle this case.
	return abacus


def partition_from_content_defects(modulus, defects):
	"""
	Constructs an e-core Partition object with the given defects. Note that the defects must add up to 0.
	"""
	return partition_from_abacus(abacus_from_content_defects(modulus, defects))

# The following partition was constructed to be an 11-core with content defects vector given by (4, 3, -5, 6, -1, -2, -3, -6, 1, 1, 2).

# p = Partition((58, 48, 46, 39, 37, 30, 29, 29, 29, 23, 22, 22, 22, 22, 22, 18, 17, 17, 17, 17, 17, 13, 12, 12, 12, 12, 12, 9, 9, 8, 8, 8, 8 , 6, 6, 6, 5, 5, 5, 5, 5, 4, 4, 4, 4, 3, 3, 3, 3, 3, 2, 2, 2, 2, 1, 1, 1, 1, 1))
# The typo above was in typing, not in my notes.

p_1 = Partition((58, 48, 46, 39, 37, 30, 29, 29, 29, 23, 22, 22, 22, 22, 22, 18, 17, 17, 17, 17, 17, 13, 12, 12, 12, 12, 12, 9, 9, 8, 8, 8, 8, 8 , 6, 6, 6, 5, 5, 5, 5, 5, 4, 4, 4, 4, 3, 3, 3, 3, 3, 2, 2, 2, 2, 1, 1, 1, 1, 1))

# The following partition is from the example on page 1899 of Brundan & Kleshchev, Graded decomposition numbers for cyclotomic Hecke algebras.
p_2 = partition_from_abacus([-10, -7, -6, -5, -1, 0, 1, 2, 5, 6, 11])

# Check for comparison with p_1 - they should be the same.
p_3 = partition_from_content_defects(11, (4, 3, -5, 6, -1, -2, -3, -6, 1, 1, 2))

import random
def random_core(modulus, lower_defect, upper_defect):
	defects = [random.randrange(lower_defect, upper_defect) for i in range(modulus-1)]
	s = -sum(defects)
	trials = 0
	while s<lower_defect or s >= upper_defect:
		trials += 1
		defects = [random.randrange(lower_defect, upper_defect) for i in range(modulus-1)]
		s = -sum(defects)
	print(trials)
	defects.append(s)
	return partition_from_content_defects(modulus, defects)

class LinearCombinationOfPartitions(object):
	"""
	Represents an (integer) linear combination of partitions. This will be used for representing Fock Spaces.

	Addition and scalar multiplication by integers is supported; for scalar multiplication, the scalar will be
	assumed to be on the left.
	"""
	def __init__(self, d):
		"""
		Accepts a dictionary of Partition to multiplicities.
		"""
		assert isinstance(d, dict)
		# For loop is used because we also check for 0's to strip them out.
		# set() is required because the dictionary changes size during iteration.
		for key in set(d.keys()):
			assert isinstance(key, Partition)
			assert isinstance(d[key], int)
			if d[key]==0:
				del d[key]
		self.d = d
	def __add__(self, other):
		partitions = set(self.d.keys())
		partitions.update(other.d.keys())
		d = {}
		for partition in partitions:
			d[partition] = self.d.get(partition, 0)+other.d.get(partition, 0)
		return LinearCombinationOfPartitions(d)
	def __rmul__(self, scalar):
		d = {}
		for partition in self.d.keys():
			d[partition] = scalar*self.d[partition]
		return LinearCombinationOfPartitions(d)
	def __neg__(self): return (-1)*self
	def __floordiv__(self, n):
		d = {}
		for partition in self.d.keys():
			d[partition] = self.d[partition]//n
		return LinearCombinationOfPartitions(d)
	def __repr__(self): return "LinearCombinationOfPartitions(%r)" % (self.d,)
	def __str__(self): return "+".join("%s*%s"%(self.d[key], key.parts) for key in sorted(self.d.keys()))
	def __eq__(self, other):
		return all(self.d.get(i, 0) == other.d.get(i, 0) for i in set(self.d.keys()).union(set(other.d.keys())))
	def __hash__(self): 
		l = list(self.d.items())
		l.sort()
		return hash(tuple(l))
	def __lt__(self, other):
		li1 = list(self.d.items())
		li1.sort()
		li2 = list(other.d.items())
		li2.sort()
		return li1<li2
	def inner_product(self, other):
		"""
		Returns the inner product according to the rule that the partitions form an orthonormal basis.
		"""
		partitions = set(self.d.keys())
		partitions.intersection_update(other.d.keys())
		inner_product = 0
		for p in partitions:
			inner_product += (self.d[p]*other.d[p])
		return inner_product
	# Induction and restriction functions: I'll just use the functions from the Partition class. This isn't
	# very efficient, but it's a first pass.
	def induct(self, index):
		"""
		Applies partition.induct() linearly to each term.
		"""
		d = dict()
		for partition in self.d.keys():
			multiplicity = self.d[partition]
			for inducted in partition.induct(index):
				d[inducted] = d.get(inducted, 0) + multiplicity
		return LinearCombinationOfPartitions(d)
	def restrict(self, index):
		"""
		Applies partition.restrict() linearly to each term.
		"""
		d = dict()
		for partition in self.d.keys():
			multiplicity = self.d[partition]
			for restricted in partition.restrict(index):
				d[restricted] = d.get(restricted, 0) + multiplicity
		return LinearCombinationOfPartitions(d)
	def modular_induct(self, modulus, index):
		"""
		Applies partition.modular_induct() linearly to each term.
		"""
		d = dict()
		for partition in self.d.keys():
			multiplicity = self.d[partition]
			for inducted in partition.modular_induct(modulus, index):
				d[inducted] = d.get(inducted, 0) + multiplicity
		return LinearCombinationOfPartitions(d)
	def modular_restrict(self, modulus, index):
		"""
		Applies partition.modular_restrict() linearly to each term.
		"""
		d = dict()
		for partition in self.d.keys():
			multiplicity = self.d[partition]
			for restricted in partition.modular_restrict(modulus, index):
				d[restricted] = d.get(restricted, 0) + multiplicity
		return LinearCombinationOfPartitions(d)

empty_partition_delta = LinearCombinationOfPartitions({Partition(()) : 1})

class FockSpace(object):
	"""
	Represents the Fock Space representation of affine sl_e. The main difference between this and LinearCombinationOfPartitions is
	this class remembers e, the modulus.
	"""
	def __init__(self, partitions, modulus):
		assert isinstance(modulus, int)
		assert modulus >= 0 # Note that 0 or 1 is allowed.
		self.e = modulus
		if isinstance(partitions, LinearCombinationOfPartitions):
			self.p = partitions
		elif isinstance(partitions, dict):
			self.p = LinearCombinationOfPartitions(partitions)
		else:
			assert False # TODO better error
	def __add__(self, other):
		return FockSpace(self.p+other.p, self.e)
	def __rmul__(self, scalar):
		return FockSpace(scalar*self.p, self.e)
	def __neg__(self): return (-1)*self
	def __floordiv__(self, n): return FockSpace(self.p//n, self.e)
	def __repr__(self): return "FockSpace(%r, %r)" % (self.p, self.e)
	def __str__(self): return str(self.p)+(" in characteristic %s." % (self.e,))
	def __eq__(self, other): return (self.e == other.e) and (self.p==other.p)
	def __hash__(self):
		return hash((self.p, self.e))
	def __lt__(self, other):
		return (self.e, self.p) < (other.e, other.p)
	def inner_product(self, other):
		"""
		Returns the inner product according to the rule that the partitions form an orthonormal basis.
		"""
		return self.p.inner_product(other.p)
	# Induction and restriction functions are automatically modular, with modulus the stored modulus.
	def induct(self, index):
		"""
		Applies partition.induct() linearly to each term.
		"""
		return FockSpace(self.p.modular_induct(self.e, index), self.e)
	def restrict(self, index):
		"""
		Applies partition.restrict() linearly to each term.
		"""
		return FockSpace(self.p.modular_restrict(self.e, index), self.e)
	# Divided powers. Not efficient at all, so TODO make this more efficient if needed.
	def divided_induct(self, index, exponent):
		"""
		Divided powers induction function. The index, usually written as a subscript, comes first, then the exponent.

		This requires the modulus be at least 2.
		"""
		if (exponent == 0): return self
		fac = 1
		power = self
		for i in range(exponent):
			fac *= (i+1)
			power = power.induct(index)
		power = power//fac
		return power
	def divided_restrict(self, index, exponent):
		"""
		Divided powers restriction function. The index, usually written as a subscript, comes first, then the exponent.

		This requires the modulus be at least 2.
		"""
		if (exponent == 0): return self
		fac = 1
		power = self
		for i in range(exponent):
			fac *= (i+1)
			power = power.restrict(index)
		power = power//fac
		return power

def evaluate_inducts(vector, modulus):
	"""
	Performs a series of modular inductions specified by a vector, with divided powers utilized when possible.

	A FockSpace object is returned.
	"""
	repeats = 0
	previous_index = None
	current_fock = FockSpace(LinearCombinationOfPartitions({Partition(()) : 1}), modulus)
	for i in vector:
		if i == previous_index:
			repeats += 1
		else:
			current_fock = current_fock.divided_induct(previous_index, repeats)
			repeats = 1
			previous_index = i
	if repeats > 0: # in other words, if vector != ()
		current_fock = current_fock.divided_induct(previous_index, repeats)
	return current_fock

def compute_idempotents(previous_idempotents, modulus):
	"""
	Iteratively computes the idempotents in the cyclotomic quiver hecke algebras;
	given the idempotents in H_{n-1}, return the idempotents in H_n.

	To get started, just pass in an iterable consisting of a single empty iterable, and the modulus.
	"""
	#next_idemps = []
	#for idempotent in previous_idempotents:
	#	for i in range(modulus):
	#		next_idemp = idempotent + (i,)
	#		if evaluate_inducts(next_idemp, modulus).p.d:
	#			next_idemps.append(next_idemp)
	#return next_idemps

	# Instead of doing the above, we rearrange idempotents so that Cartan matrix
	# arranges itself into blocks, and duplicates are adjacent.
	#
	# We construct a nested structure of dictionaries with the following structure:
	# { block : {fock_space_element : [idempotent_1, idempotent_2, ...], ... }, ...}
	# The blocks are parameterized by the multiplicities of each index in the vectors.
	next_idemps_clusterfuck = {}
	for idempotent in previous_idempotents:
		for i in range(modulus):
			next_idemp = idempotent + (i,)
			fock_space_element = evaluate_inducts(next_idemp, modulus)
			if fock_space_element.p.d:
				block = tuple(sum(j==index for j in next_idemp) for index in range(modulus))
				if block in next_idemps_clusterfuck:
					if fock_space_element in next_idemps_clusterfuck[block]:
						next_idemps_clusterfuck[block][fock_space_element].append(next_idemp)
					else:
						next_idemps_clusterfuck[block][fock_space_element] = [next_idemp]
				else:
					next_idemps_clusterfuck[block] = {fock_space_element : [next_idemp]}
	next_idemps = []
	for block in next_idemps_clusterfuck.keys():
		for fock_space_element in next_idemps_clusterfuck[block].keys():
			for idempotent in next_idemps_clusterfuck[block][fock_space_element]:
				next_idemps.append(idempotent)
	return next_idemps

def compute_cartan_matrix(idempotents, modulus):
	"""
	Given the output of compute_idempotents, return the dimensions of hom spaces between the corresponding projectives,
	after taking divided powers.

	Cartan matrix isn't the right word, because these are not the indecomposable projectives, and they come with duplicates, but
	I'm sticking with that choice of word until I know of a better one.
	"""
	fock_space_elts = tuple(evaluate_inducts(i, modulus) for i in idempotents)
	return [[i.inner_product(j) for i in fock_space_elts] for j in fock_space_elts]

def compute_reduced_cartan_matrix(idempotents, modulus):
	"""
	Given the output of compute_idempotents, return the dimensions of hom spaces between the corresponding projectives,
	after taking divided powers. Unlike compute_cartan_matrix(), here we eliminate duplicate fock space elements from
	consideration, which reduces the size of the matrix.
	"""
	fock_space_elts = list(evaluate_inducts(i, modulus) for i in idempotents)
	i = 1
	while i < len(fock_space_elts):
		if fock_space_elts[i] == fock_space_elts[i-1]:
			del fock_space_elts[i]
		else:
			i += 1
	return [[i.inner_product(j) for i in fock_space_elts] for j in fock_space_elts]

import sys
#e = 2
#while True:
#	print("At modulus %s." % e)
#	previous_idempotents = [()]
#	level = 0
#	cartan_matrix = []
#	while len(cartan_matrix) <= 50:
#		print("At level %s for mod %s." % (level, e))
#		for i, idemp in enumerate(previous_idempotents):
#			print("v_%s: %s" % (i, idemp))
#			sys.stdout.flush()
#		for i, idemp in enumerate(previous_idempotents):
#			print("e_{v_%s}(\emptyset) = %s" % (i, evaluate_inducts(idemp, e)))
#			sys.stdout.flush()
#		cartan_matrix = compute_reduced_cartan_matrix(previous_idempotents, e)
#		print("Reduced Cartan matrix:")
#		print("["+"\n ".join(map(str, cartan_matrix)) + "]")
#		sys.stdout.flush()
#		previous_idempotents = compute_idempotents(previous_idempotents, e)
#		level += 1
#	e += 1

# The function compute_reduced_cartan_matrix eliminated duplicate rows from the matrix.
# Next I want to incorporate the Crystal graph, to compute a true Z-basis of the Grothendieck group.
# This will eliminate all excessive rows from the matrix. *

# I am guided by the description of the Crystal graph given in Kleshchev's book
# "Linear and Projective Representations of Symmetric Groups", Chapter 11.
# Iteratively computing the Crystal graph will require that the appropriate
# idempotents come equipped with their associated partitions.
# * Looking at the case p=2, n=7, it is apparent that the crystal graph does *not*
# give a basis. Nevertheless, it will at least reduce the matrix.

def compute_crystal(modulus, previous_crystal=None):
	"""
	Computes the next row of the crystal given the previous row. The format of each term of the
	crystal here is an ordered pair (idempotent, partition), consisting of an idempotent
	as in compute_idempotents(), and the associated modulus-regular partition represented as a
	Partition object.

	To get started from the 0-th row, simply do not pass in a previous_crystal. Then the first row
	will be returned.
	"""
	next_crystal = []
	if previous_crystal == None:
		previous_crystal = [((), Partition(()))]
	for (previous_idempotent, previous_partition) in previous_crystal:
		for index in range(modulus):
			partition = previous_partition.crystal_induct(modulus, index)
			if partition:
				next_crystal.append(((previous_idempotent + (index,)), partition))
	# Sort idempotents by blocks and then by fock space elements.
	next_crystal.sort(key = lambda pair : (tuple(sum(j==index for j in pair[0]) for index in range(modulus)), # block
	                                       pair[1], # partition
	                                       evaluate_inducts(pair[0], modulus), # fock space element
	                                       pair[0]))
	return next_crystal

def print_matrix(matrix):
	"""
	Prints the matrix with columns aligned.
	"""
	offsets = tuple(map(str, (max(len(str(matrix[i][j])) for i in range(len(matrix))) for j in range(len(matrix)))))
	form = "["+ ", ".join("%"+offsets[i] + "s" for i in range(len(matrix)))+"]"
	print("["+",\n ".join(form % tuple(line) for line in matrix) + "]")

e = 2
while True:
	print("At modulus %s." % e)
	previous_idempotents = [((), Partition(()))]
	level = 0
	cartan_matrix = []
	while len(cartan_matrix) <= 50:
		print("At level %s for mod %s." % (level, e))
		for i, (idemp, part) in enumerate(previous_idempotents):
			print("w_%s: %s" % (i, idemp))
			sys.stdout.flush()
		for i, (idemp, part) in enumerate(previous_idempotents):
			print("w_%s crystal node: %s" % (i, part.parts))
			sys.stdout.flush()
		for i, (idemp, part) in enumerate(previous_idempotents):
			print("e_{w_%s}(\emptyset) = %s" % (i, evaluate_inducts(idemp, e)))
			sys.stdout.flush()
		cartan_matrix = compute_reduced_cartan_matrix(map(lambda pair : pair[0], previous_idempotents), e)
		print("Reduced (Crystal) Cartan matrix:")
		#print("["+",\n ".join(map(str, cartan_matrix)) + "]")
		print_matrix(cartan_matrix)
		sys.stdout.flush()
		previous_idempotents = compute_crystal(e, previous_idempotents)
		level += 1
	e += 1

if __name__=='__main__':
	import code
	code.interact(local=globals())
