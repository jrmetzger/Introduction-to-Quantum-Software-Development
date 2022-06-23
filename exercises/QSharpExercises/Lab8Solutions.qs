// Solutions for Lab 8: The Quantum Fourier Transform
// Copyright 2021 The MITRE Corporation. All Rights Reserved.

namespace QSharpExercises.Solutions.Lab8 {

    open Microsoft.Quantum.Arithmetic;
    open Microsoft.Quantum.Canon;
    open Microsoft.Quantum.Convert;
    open Microsoft.Quantum.Intrinsic;
    open Microsoft.Quantum.Math;
    open Microsoft.Quantum.Measurement;


    /// # Summary
    /// In this exercise, you must implement the Quantum Fourier Transform
    /// circuit. This will perform an in-place transformation of the
    /// amplitudes of each state in the superposition from the
    /// value-versus-time to the value-versus-frequency domain.
    /// 
    /// # Input
    /// ## register
    /// A register containing qubits in superposition.
    /// The superposition is unknown, and the amplitudes are not guaranteed to
    /// be uniform.
    operation Exercise1 (register : BigEndian) : Unit is Adj + Ctl {
        for i in 0..Length(register!) - 1 {
            // Each qubit starts with a Hadamard
            H(register![i]);

            // Go through the rest of the qubits that follow this one,
            // we're going to use them as control qubits on phase-shift
            // gates. The phase-shift gate is basically a gate that rotates
            // the |1> portion of a qubit's state around the Z axis of the
            // Bloch sphere by Φ, where Φ is the angle from the +X axis on
            // the X-Y plane. Q# actually provides this gate as the R1
            // function, and for convenience when Φ = kπ/2^m for some
            // numbers k and m, they provide the R1Frac function which just
            // lets you specify k and m directly.
            // 
            // For more info on the phase-shift gate, look at the "phase shift"
            // section of this Wiki article and the MSDN page for R1Frac:
            // https://en.wikipedia.org/wiki/Quantum_logic_gate
            // https://docs.microsoft.com/en-us/qsharp/api/prelude/microsoft.quantum.primitive.r1frac
            for j in i + 1..Length(register!) - 1 {
                // According to the circuit diagram, the controlled R1 gates
                // change the "m" value as described above. The first one
                // is always 2, and then it iterates from there until the
                // last one.
                let m = j - i + 1;

                // Perform the rotation, controlled by the jth qubit on the
                // ith qubit, with e^(2πi/2^m)
                Controlled R1Frac([register![j]], (2, m, register![i]));
            }
        }

        // The bit order is going to be backwards after the QFT so this just
        // reverses it.
        SwapReverseRegister(register!);
    }


    /// # Summary
    /// In this exercise, you are given a quantum register in an unknown
    /// superposition. In this superposition, a single sine wave has been
    /// encoded into the amplitudes of each term in the superposition.
    /// 
    /// For example: the first sample of the wave will be the amplitude of the
    /// |0> term, the second sample of the wave will be the amplitude of the
    /// |1> term, the third will be the amplitude of the |2> term, and so on.
    /// 
    /// Your goal is to find the frequency of these samples, and return that
    /// frequency.
    /// 
    /// # Input
    /// ## register
    /// The register which contains the samples of the sine wave in the
    /// amplitudes of  its terms.
    /// 
    /// ## sampleRate
    /// The number of samples per second that were used to collect the
    /// original samples. You will need this to retrieve the correct
    /// frequency.
    /// 
    /// # Output
    /// The frequency of the sine wave.
    operation Exercise2 (
        register : BigEndian,
        sampleRate : Double
    ) : Double {
        // Run the inverse QFT, which corresponds to the normal DFT
        Adjoint Exercise1(register);

        // Measure the result from QFT
        let numberOfStates = IntAsDouble(2 ^ Length(register!));
        let registerLE = BigEndianAsLittleEndian(register);
        mutable result = IntAsDouble(MeasureInteger(registerLE));

        // QFT suffers from the same Nyquist-frequency mirroring as DFT, but
        // we can't just look at all of the output details and ignore the
        // mirrored results. If we end up measuring a mirrored result, this
        // will flip it back to the proper result in the 0 < X < N/2 space.
        if (result > numberOfStates / 2.0) {
            set result = numberOfStates - result;
        }

        // Correct for the sample rate.
        let totalTime = numberOfStates / sampleRate;
        set result = result / totalTime;
        return result;
    }
}