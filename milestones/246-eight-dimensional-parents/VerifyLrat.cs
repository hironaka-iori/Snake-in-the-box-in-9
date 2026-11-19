// Independently check the positive-hint (ordered RUP) fragment of ASCII LRAT.
// Arguments: a standard DIMACS CNF file and a gzip-compressed LRAT file.
using System;
using System.Collections.Generic;
using System.IO;
using System.IO.Compression;
using System.Text;

class VerifyLrat {
    sealed class Tokens {
        readonly string line;
        int pos;
        public Tokens(string line) { this.line = line; }
        void Space() {
            while (pos < line.Length && char.IsWhiteSpace(line[pos])) ++pos;
        }
        public bool End() { Space(); return pos == line.Length; }
        public bool Tag(char tag) {
            Space();
            if (pos >= line.Length || line[pos] != tag ||
                (pos+1 != line.Length && !char.IsWhiteSpace(line[pos+1]))) return false;
            ++pos;
            return true;
        }
        public int Number() {
            Space();
            bool minus = pos < line.Length && line[pos] == '-';
            if (minus) ++pos;
            int start = pos, n = 0;
            while (pos < line.Length && line[pos] >= '0' && line[pos] <= '9') {
                int d = line[pos++] - '0';
                if (n > (int.MaxValue-d)/10) throw new InvalidDataException("integer overflow");
                n = n*10 + d;
            }
            if (pos == start || (minus && n == 0) ||
                (pos < line.Length && !char.IsWhiteSpace(line[pos])))
                throw new InvalidDataException("invalid integer or missing terminator");
            return minus ? -n : n;
        }
    }

    readonly Dictionary<int, int[]> db = new Dictionary<int, int[]>();
    int varCount, originalCount, lastAdded, stamp;
    int[] marked;
    sbyte[] sign;
    long additions, deletions, hints, inputLine;
    int provedEmpty;
    string stage;

    void Literal(int lit) {
        if (Math.Abs(lit) > varCount) throw new InvalidDataException("variable outside CNF range");
    }

    void ReadCnf(string filename) {
        stage = "CNF";
        bool header = false;
        var clause = new List<int>();
        using (var input = new StreamReader(filename, Encoding.ASCII)) {
            string line;
            while ((line = input.ReadLine()) != null) {
                ++inputLine;
                var t = new Tokens(line);
                if (t.End() || t.Tag('c')) continue;
                if (!header) {
                    var fields = line.Split((char[])null, StringSplitOptions.RemoveEmptyEntries);
                    if (fields.Length != 4 || fields[0] != "p" || fields[1] != "cnf" ||
                        !int.TryParse(fields[2], out varCount) || !int.TryParse(fields[3], out originalCount) ||
                        varCount < 0 || originalCount < 0) throw new InvalidDataException("bad DIMACS header");
                    header = true;
                    continue;
                }
                while (!t.End()) {
                    int n = t.Number();
                    if (n == 0) {
                        if (lastAdded == originalCount) throw new InvalidDataException("extra input clause");
                        db.Add(++lastAdded, clause.ToArray());
                        clause.Clear();
                    } else {
                        Literal(n);
                        clause.Add(n);
                    }
                }
            }
        }
        if (!header || clause.Count != 0 || lastAdded != originalCount)
            throw new InvalidDataException("incomplete DIMACS data");
        marked = new int[checked(varCount+1)];
        sign = new sbyte[marked.Length];
    }

    // Returns false precisely when the opposite literal was already assigned.
    bool Assign(int lit) {
        int v = Math.Abs(lit);
        sbyte value = (sbyte)(lit > 0 ? 1 : -1);
        if (marked[v] == stamp) return sign[v] == value;
        marked[v] = stamp;
        sign[v] = value;
        return true;
    }

    // Returns true for a falsified hint, otherwise assigns its unique unit.
    bool Propagate(int[] clause) {
        int open = 0;
        foreach (int lit in clause) {
            int v = Math.Abs(lit);
            if (marked[v] != stamp) {
                if (open != 0 && open != lit) throw new InvalidDataException("non-unit hint");
                open = lit;
            } else if ((sign[v] > 0) == (lit > 0)) {
                throw new InvalidDataException("satisfied hint");
            }
        }
        if (open == 0) return true;
        if (!Assign(open)) throw new InvalidDataException("inconsistent unit");
        return false;
    }

    void ReadProof(string filename) {
        stage = "LRAT";
        inputLine = 0;
        var clause = new List<int>();
        using (var raw = File.OpenRead(filename))
        using (var gz = new GZipStream(raw, CompressionMode.Decompress))
        using (var input = new StreamReader(gz, Encoding.ASCII)) {
            string line;
            while ((line = input.ReadLine()) != null) {
                ++inputLine;
                var t = new Tokens(line);
                if (t.End() || t.Tag('c')) continue;
                int id = t.Number();
                if (id < 0) throw new InvalidDataException("negative step ID");
                if (t.Tag('d')) {
                    int deleted;
                    while ((deleted = t.Number()) != 0) {
                        if (deleted < 0 || !db.Remove(deleted)) throw new InvalidDataException("deleting unknown clause");
                        ++deletions;
                    }
                    if (!t.End()) throw new InvalidDataException("extra deletion fields");
                    continue;
                }
                if (id <= lastAdded) throw new InvalidDataException("non-increasing addition ID");
                if (stamp == int.MaxValue) { Array.Clear(marked, 0, marked.Length); stamp = 0; }
                ++stamp;
                clause.Clear();
                int lit;
                bool conflict = false;
                while ((lit = t.Number()) != 0) {
                    Literal(lit);
                    clause.Add(lit);
                    if (!Assign(-lit)) conflict = true;
                }
                int hint;
                while ((hint = t.Number()) != 0) {
                    if (hint < 0) throw new InvalidDataException("negative RAT hint unsupported");
                    int[] justified;
                    if (!db.TryGetValue(hint, out justified)) throw new InvalidDataException("unknown hint ID");
                    if (conflict) throw new InvalidDataException("hint after conflict");
                    conflict = Propagate(justified);
                    ++hints;
                }
                if (!t.End() || !conflict) throw new InvalidDataException("unproved addition");
                db.Add(id, clause.ToArray());
                lastAdded = id;
                ++additions;
                if (clause.Count == 0) provedEmpty = id;
            }
        }
        if (provedEmpty == 0) throw new InvalidDataException("no proved empty clause");
    }

    static int Main(string[] args) {
        var check = new VerifyLrat();
        try {
            if (args.Length != 2) throw new ArgumentException("usage: VerifyLrat model.cnf proof.lrat.gz");
            check.ReadCnf(args[0]);
            check.ReadProof(args[1]);
            Console.WriteLine("VERIFIED UNSAT variables={0} input_clauses={1} additions={2} deleted_clauses={3} hints={4} empty_id={5}",
                check.varCount, check.originalCount, check.additions, check.deletions, check.hints, check.provedEmpty);
            return 0;
        } catch (Exception error) {
            Console.Error.WriteLine("REJECT {0} line {1}: {2}", check.stage, check.inputLine, error.Message);
            return 1;
        }
    }
}
