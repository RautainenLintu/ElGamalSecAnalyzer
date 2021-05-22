import time
import random
import math


# Downloads factor base from "prime.txt" and returns it as a list
def download_factorbase(filename):
    f = open(filename)
    base = f.read().split(" ")
    intbase = []
    for i in base:
        intbase.append(int(i))
    f.close()
    return intbase


# Asks for timeout for each of the methods
def attacks_timeout_input():
    print("The program requires timeout for each method. If timeout is set to 0, the method is not applied.")
    print("Enter timeout for Vinogradov-Shanks method:")
    time_vs = int(input())
    print("Enter timeout for Pohlig-Hellman method:")
    time_ph = int(input())
    print("Enter timeout for rho-Pollard method:")
    time_rho = int(input())
    return time_vs, time_ph, time_rho


# Applies Vinogradov-Shanks attack to given public key
def vinogradov_shanks_method(y, g, p, time_vs, report):
    report.write("Vinogradov-Shanks method is being applied...\n")
    initial_time = time.time()
    m = math.floor(math.sqrt(p)) + 1
    report.write('m = {0}\n'.format(m))
    g_pow_m = pow(g, m, p)
    report.write('g^m = = {0}\n'.format(g_pow_m))
    gamma = g_pow_m
    # values of gamma and i are stored in dictionary as keys and values
    dict_g_pow_im = {}
    i = 1
    report.write("Computing g^im...\n")
    while i <= m:
        if time.time() - initial_time >= time_vs:
            report.write("Vinogradov-Shanks method unsuccessful due to timeout.\n")
            return 0
        dict_g_pow_im[gamma] = i
        report.write('\ti = {0}\n'.format(i))
        report.write('\tgamma = g^im = {0}\n'.format(gamma))
        gamma = (gamma * g_pow_m) % p
        i += 1
    j = 0
    report.write("Computing y * g^j...\n")
    while j <= m - 1:
        if time.time() - initial_time >= time_vs:
            report.write("Vinogradov-Shanks method unsuccessful due to timeout.\n")
            return 0
        report.write('\tj = {0}\n'.format(j))
        y_g_j = (y * pow(g, j, p)) % p
        report.write('\ty * g^j = {0}\n'.format(y_g_j))
        if y_g_j in dict_g_pow_im.keys():
            report.write("Vinogradov-Shanks attack successful! Secret key x is found.\n")
            x = (dict_g_pow_im[y_g_j] * m - j) % (p - 1)
            report.write('x = {0}\n'.format(x))
            return x
        else:
            report.write("\tNo match. Increasing j.\n")
            j += 1
    report.write("Solution not found. Vinogradov-Shanks method is not applicable.\n")
    report.write("...\n")
    return 0


# Auxiliary function for Pohlig-Hellman method: finds a factorization of p - 1
def factorize_p_minus_1(p, initial_time, time_ph):
    remainder = p - 1
    factorbase = download_factorbase("primes.txt")
    # factors and its powers are stored in dict
    factors = {}
    pow = 0
    for prime in factorbase:
        if time.time() - initial_time >= time_ph:
            # if the factorization takes too long, it is interrupted due to timeout
            return {0: 0}
        if remainder <= 0:
            break
        while remainder % prime == 0:
            pow += 1
            remainder = remainder // prime
        if pow > 0:
            factors[prime] = pow
        pow = 0
    return factors


# Applies Pohlig-Hellman attack to given public key
def pohlig_hellman_method(y, g, p, time_ph, report):
    report.write("Pohlig-Hellman method is being applied...\n")
    initial_time = time.time()
    # Let us change the letters according to those used in lectures.
    h, a = y, g
    factors = factorize_p_minus_1(p, initial_time, time_ph)
    if factors == {0: 0}:
        report.write("Pohlig-Hellman method unsuccessful due to timeout.\n")
        return 0
    report.write("Factorization of p - 1 computed:\n")
    report.write("p - 1 = ")
    report.write("1")
    for prime in factors:
        report.write(' * {0} ^ {1}'.format(prime, factors[prime]))
    report.write("\n")
    # logarithms modulo p_i ** k_i are stored in dict
    logarithms = {}
    report.write("Let us consider logarithms modulo p_i ** k_i...\n")
    for p_i in factors.keys():
        if time.time() - initial_time >= time_ph:
            report.write("Pohlig-Hellman method unsuccessful due to timeout.\n")
            return 0
        report.write('p_i = {0}\n'.format(p_i))
        k_i = factors[p_i]
        report.write('k_i = {0}\n'.format(k_i))
        h_i = h
        coefficients_c = []
        report.write('Table of j and A_j is being computed for p_i = {0}, k_i = {1}\n'.format(p_i, k_i))
        table = {}
        for j in range(p_i):
            if time.time() - initial_time >= time_ph:
                report.write("Pohlig-Hellman method unsuccessful due to timeout.\n")
                return 0
            A_j = pow(a, ((p - 1) * j) // p_i, p)
            table[A_j] = j
            report.write('\tA[j] = {0} , j = {1}\n'.format(A_j, j))
        for i in range(k_i):
            if time.time() - initial_time >= time_ph:
                report.write("Pohlig-Hellman method unsuccessful due to timeout.\n")
                return 0
            c_i = table[pow(h_i, (p - 1) // (p_i ** (i + 1)), p)]
            report.write('\t\ti = {0}\n'.format(i))
            report.write('\t\th_i = {0}\n'.format(h_i))
            report.write('\t\tc_i = {0}\n'.format(c_i))
            coefficients_c.append(c_i)
            h_i = h_i * pow(a, -(p_i ** i) * c_i, p) % p
        report.write('\t\tCoefficients c: {0}\n'.format(coefficients_c))
        report.write("\n")
        log = 0
        for i in range(k_i):
            if time.time() - initial_time >= time_ph:
                report.write("Pohlig-Hellman method unsuccessful due to timeout.\n")
                return 0
            log = log * p_i + coefficients_c[(k_i - 1) - i]
        logarithms[p_i] = log
    for p_i in logarithms:
        report.write('x = {0} (mod {1})\n'.format(logarithms[p_i], p_i ** k_i))
    report.write("Applying CRT to the system of equations...\n")
    x = 0
    for p_i in factors.keys():
        if time.time() - initial_time >= time_ph:
            report.write("Pohlig-Hellman method unsuccessful due to timeout.\n")
            return 0
        k_i = factors[p_i]
        a_i = p_i ** k_i
        m_i = (p - 1) // a_i
        x += logarithms[p_i] * m_i * pow(m_i, -1, a_i)
        x %= (p - 1)
    report.write("Pohlig-Hellman attack successful! Secret key x is found.\n")
    report.write('x = {0}\n'.format(x))
    return x


# Retrieves 3 sequences up to element sequence[index]
def retrieve_missing_elements_of_seq(h_sequence, x_sequence, y_sequence, a, h, p, index):
    while len(h_sequence) - 1 < index:
        h_i = h_sequence[len(h_sequence) - 1]
        x_i = x_sequence[len(x_sequence) - 1]
        y_i = y_sequence[len(y_sequence) - 1]
        if 0 <= h_i < p // 3:
            h_i = (h * h_i) % p
            # x_i = x_i
            y_i = (y_i + 1) % (p - 1)
        elif p // 3 <= h_i < 2 * p // 3:
            h_i = (h_i ** 2) % p
            x_i = (x_i * 2) % (p - 1)
            y_i = (y_i * 2) % (p - 1)
        else:
            h_i = (a * h_i) % p
            x_i = (x_i + 1) % (p - 1)
            # y_i = y_i
        h_sequence.append(h_i)
        x_sequence.append(x_i)
        y_sequence.append(y_i)


# gets q for every j on 0 <= j <= math.floor(math.log2(s))
def get_q(s):
    q = {}
    for j in range(0, math.floor(math.log2(s)) + 1):
        q[j] = math.floor(s // 2 ** j)
        if math.gcd(q[j], 2) != 1:
            q[j] -= 1
    return q


# gets set s^ for number s
def get_s_circonflexe(q: dict, s):
    s_circ = {}
    for j in range(0, math.floor(math.log2(s)) + 1):
        s_circ[j] = q[j] * 2 ** j - 1
    return s_circ


# Applies Rho Pollard method
def rho_pollard_method(y, g, p, time_rho, report):
    report.write("Rho-Pollard method is being applied...\n")
    initial_time = time.time()
    # Let us change the letters according to those used in lectures.
    a, h = g, y
    phi = p - 1
    h_sequence = []
    x_sequence = []
    y_sequence = []
    x_i, y_i, h_i = 0, 0, 1
    h_sequence.append(h_i)
    x_sequence.append(x_i)
    y_sequence.append(y_i)
    s = 1
    while s <= p:
        if time.time() - initial_time >= time_rho:
            report.write("Rho Pollard method unsuccessful due to timeout.\n")
            return 0
        report.write('s = {0}\n'.format(s))
        retrieve_missing_elements_of_seq(h_sequence, x_sequence, y_sequence, a, h, p, s)
        q = get_q(s)
        s_circ_set = get_s_circonflexe(q, s)
        report.write('s^ = {0}\n'.format(s_circ_set))
        index = max(s_circ_set.values())
        retrieve_missing_elements_of_seq(h_sequence, x_sequence, y_sequence, a, h, p, index)
        h_i, x_i, y_i = h_sequence[len(h_sequence) - 1], x_sequence[len(x_sequence) - 1], y_sequence[len(y_sequence) - 1]
        report.write('h_i, x_i, y_i = {0}, {1}, {2}\n'.format(h_i, x_i, y_i))
        report.write('h_sequence = {0}\n'.format(h_sequence))
        report.write('x_sequence = {0}\n'.format(x_sequence))
        report.write('y_sequence = {0}\n'.format(y_sequence))
        for t in s_circ_set.values():
            if time.time() - initial_time >= time_rho:
                report.write("Rho Pollard method unsuccessful due to timeout.\n")
                return 0
            if h_sequence[t] == h_sequence[s]:
                delta_x = (x_sequence[s] - x_sequence[t]) % phi
                delta_y = (y_sequence[s] - y_sequence[t]) % phi
                if delta_x == 0 or delta_y == 0:
                    log_a_h = 0
                    report.write('log = {0}\n'.format(log_a_h))
                    return 0
                gcd = math.gcd(delta_y, phi)
                if gcd != 1:
                    phi = phi // gcd
                log = (- delta_x * pow(delta_y, -1, phi)) % phi
                for i in range(gcd):
                    log_a_h = log + i * phi
                    if pow(a, log_a_h, p) == (h % p):
                        report.write('log = {0}\n'.format(log_a_h))
                        return log_a_h % (p - 1)
        s += 1


# generates keys using the list of suitable primes (primes of necessary size)
def generate_keys(suitable_primes, factorbase):
    index = random.randint(0, len(suitable_primes) - 1)
    p = suitable_primes[index]
    phi = p - 1
    g_found = False
    while not g_found:
        g = random.randint(2, p - 1)
        print("g = ", g)
        for prime in factorbase:
            if prime > phi:
                g_found = True
                print("Found!")
                break
            L = phi / prime
            if phi / prime % 1 != 0:
                continue
            print("prime =", prime)
            print("L = ", L)
            g_l = pow(g, int(phi / prime), p)
            print("g_l = ", g_l)
            if g_l == 1:
                print("Failed. Choosing another g.")
                break
    x = random.randint(2, phi)
    y = pow(g, x, p)
    print("Public key generated: (y, g, p) = ", y, g, p)
    print("Private key generated: x = ", x)
    return y, g, p, x


while True:
    print("Choose mode 1 (analysis mode) or 2 (testing mode):")
    mode = input()
    while mode != '1' and mode != '2':
        print("Incorrect mode. Try again:")
        mode = input()
    if mode == '1':
        print("Enter y = g^x mod p:")
        y = int(input())
        print("Enter g:")
        g = int(input())
        print("Enter p:")
        p = int(input())
        # time_vs, time_ph, time_rho = attacks_timeout_input()
        # while time_vs < 0 or time_ph < 0 or time_rho < 0:
        #     print("Incorrect values. Time cannot be negative")
        #     print("Try again.")
        #     time_vs, time_ph, time_rho = attacks_timeout_input()
        # y, g, p = 25, 264, 337
        time_vs, time_ph, time_rho = 10, 10, 10
        report = open("report.txt", "w")
        report.write('(y, g, p) = {0}, {1}, {2}\n'.format(y, g, p))
        report.write('Timeout for Vinogradov-Shanks method = {0}\n'.format(time_vs))
        report.write('Timeout for Pohlig-Hellman method = {0}\n'.format(time_ph))
        report.write('Timeout for Rho Pollard method = {0}\n'.format(time_rho))
        report.write("\n")
        if time_vs != 0:
            vinogradov_shanks_method(y, g, p, time_vs, report)
            report.write("\n")
        if time_ph != 0:
            pohlig_hellman_method(y, g, p, time_ph, report)
            report.write("\n")
        if time_rho != 0:
            rho_pollard_method(y, g, p , time_rho, report)
            report.write("\n")
            report.close()

        print("Analysis completed. You can find the report in report.txt")
    if mode == '2':
        factorbase = download_factorbase("primes.txt")
        print("Factorbase downloaded.")
        print("Enter timeout for Pohlig-Hellman method:")
        time_ph = int(input())
        while time_ph <= 0:
            print("Incorrect time value. Try again")
            print("Enter timeout for Pohlig-Hellman method: ")
            time_ph = int(input())
        print("Enter size of public key in bits:")
        s_bits = int(input())
        prime_floor = 2 ** (s_bits - 1)
        prime_ceil = 2 ** s_bits - 1
        while prime_ceil > factorbase[len(factorbase) - 1]:
            print("Unfortunately, the size is too large due to limited factorbase...")
            print("Try again:")
            s_bits = int(input())
            prime_floor = 2 ** (s_bits - 1)
            prime_ceil = 2 ** s_bits - 1
        print("Lowest border of p = ", prime_floor)
        print("Highest border of p = ", prime_ceil)
        suitable_primes = []
        for prime in factorbase:
            if prime < prime_floor:
                continue
            if prime > prime_ceil:
                break
            suitable_primes.append(prime)
        print("List of possible prime numbers is downloaded.")
        report = open("report.txt", "w")
        while True:
            y, g, p, x = generate_keys(suitable_primes, factorbase)
            x_retrieved = pohlig_hellman_method(y, g, p, time_ph, report)
            print()
            if x_retrieved != 0:
                print("Pohlig-Hellman method successful")
                print("Weak key retrieved: (y, g, p) = ", y, g, p)
                print("x found: ", x_retrieved)
                break
            else:
                print("Failed. Generating another pair of keys...")
                print()
        report.close()
    print()
    print("Program finished")
    print("Press Enter to restart")
    input()

