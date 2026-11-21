// Extract the positive-RUP dependency cone of one checked empty clause.
// Each on-disk record consists of derived hints, their count, and the addition ID.
using System;
using System.Collections;
using System.IO;
using System.IO.Compression;
using System.Text;

class TrimLrat {
    struct Line {
        readonly string text;
        int pos;
        public Line(string s) { text = s; pos = 0; }
        void Skip() { while (pos < text.Length && char.IsWhiteSpace(text[pos])) ++pos; }
        public bool Empty() { Skip(); return pos == text.Length || text[pos] == 'c'; }
        public bool Deletion() {
            Skip();
            if (pos >= text.Length || text[pos] != 'd') return false;
            ++pos;
            return true;
        }
        public int Number() {
            Skip();
            bool negative = pos < text.Length && text[pos] == '-';
            if (negative) ++pos;
            int n = 0, start = pos;
            while (pos < text.Length && text[pos] >= '0' && text[pos] <= '9')
                n = checked(10*n + text[pos++] - '0');
            if (pos == start) throw new InvalidDataException("Missing integer");
            return negative ? -n : n;
        }
    }

    sealed class ReverseReader : IDisposable {
        readonly FileStream input;
        readonly byte[] block = new byte[1 << 20];
        long start = -1;
        public long Position;
        public ReverseReader(string path) {
            input = File.OpenRead(path);
            Position = input.Length;
        }
        public int Previous() {
            Position -= 4;
            if (Position < 0) throw new EndOfStreamException();
            long next = Position / block.Length * block.Length;
            if (next != start) {
                start = next;
                input.Position = start;
                int n = (int)Math.Min(block.Length, input.Length - start);
                for (int offset = 0; offset < n;) {
                    int got = input.Read(block, offset, n-offset);
                    if (got == 0) throw new EndOfStreamException();
                    offset += got;
                }
            }
            int k = (int)(Position - start);
            return block[k] | (block[k+1]<<8) | (block[k+2]<<16) | (block[k+3]<<24);
        }
        public void Dispose() { input.Dispose(); }
    }

    static StreamReader Open(string path) {
        return new StreamReader(new GZipStream(File.OpenRead(path), CompressionMode.Decompress),
                                Encoding.ASCII, false, 1 << 17);
    }

    static int Index(string path, string spool, int original) {
        int last = original;
        using (var input = Open(path))
        using (var stream = new FileStream(spool, FileMode.Create, FileAccess.Write, FileShare.None, 1 << 20))
        using (var output = new BinaryWriter(stream)) {
            string text;
            while ((text = input.ReadLine()) != null) {
                var line = new Line(text);
                if (line.Empty()) continue;
                int id = line.Number();
                if (line.Deletion()) continue;
                if (id <= last) throw new InvalidDataException("Addition IDs not increasing");
                last = id;
                bool empty = line.Number() == 0;
                if (!empty) while (line.Number() != 0) {}
                int count = 0, hint;
                while ((hint = line.Number()) != 0) {
                    if (hint < 0 || hint >= id) throw new InvalidDataException("Unsupported hint");
                    if (hint > original) { output.Write(hint); ++count; }
                }
                output.Write(count);
                output.Write(id);
                if (empty) return id;
            }
        }
        throw new InvalidDataException("No empty clause");
    }

    static BitArray Trace(string spool, int goal) {
        // 16 MiB for the bitmap at this upper limit; archives are normally much smaller.
        if (goal > 134217727) throw new InvalidDataException("Clause ID exceeds bitmap budget");
        var used = new BitArray(goal+1);
        used[goal] = true;
        using (var reader = new ReverseReader(spool)) {
            while (reader.Position > 0) {
                int id = reader.Previous(), n = reader.Previous();
                if (n < 0 || 4L*n > reader.Position) throw new InvalidDataException("Bad hint record");
                if (used[id]) {
                    for (int i = 0; i < n; ++i) used[reader.Previous()] = true;
                } else reader.Position -= 4L*n;
            }
        }
        return used;
    }

    static void Emit(string proof, string output, int goal, int original, BitArray used) {
        using (var input = Open(proof))
        using (var writer = new StreamWriter(output, false, Encoding.ASCII, 1 << 17)) {
            writer.NewLine = "\n";
            string text;
            while ((text = input.ReadLine()) != null) {
                var row = new Line(text);
                if (row.Empty()) continue;
                int id = row.Number();
                if (row.Deletion()) {
                    // The CNF remains in the checker's database. Only release kept derived clauses.
                    bool any = false;
                    int d;
                    while ((d = row.Number()) != 0) {
                        if (d > original && d<=goal && used[d]) {
                            if (!any) { writer.Write(id); writer.Write(" d"); any = true; }
                            writer.Write(' '); writer.Write(d);
                        }
                    }
                    if (any) writer.WriteLine(" 0");
                } else if (used[id]) {
                    writer.WriteLine(text);
                    if (id == goal) return;
                }
            }
        }
        throw new InvalidDataException("Final addition missing");
    }

    static int Main(string[] args) {
        try {
            if (args.Length != 4) throw new ArgumentException("expected: original-clauses proof.gz spool output.lrat");
            int original = int.Parse(args[0]);
            int goal = Index(args[1], args[2], original);
            var used = Trace(args[2], goal);
            Emit(args[1], args[3], goal, original, used);
            Console.WriteLine("Extracted empty clause " + goal);
            return 0;
        } catch (Exception e) {
            Console.Error.WriteLine(e.Message);
            return 1;
        }
    }
}
