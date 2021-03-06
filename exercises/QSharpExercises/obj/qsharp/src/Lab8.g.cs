//------------------------------------------------------------------------------
// <auto-generated>                                                             
//     This code was generated by a tool.                                       
//     Changes to this file may cause incorrect behavior and will be lost if    
//     the code is regenerated.                                                 
// </auto-generated>                                                            
//------------------------------------------------------------------------------
#pragma warning disable 436
#pragma warning disable 162
#pragma warning disable 1591
using System;
using Microsoft.Quantum.Core;
using Microsoft.Quantum.Intrinsic;
using Microsoft.Quantum.Simulation.Core;

[assembly: CallableDeclaration("{\"Kind\":{\"Case\":\"Operation\"},\"QualifiedName\":{\"Namespace\":\"QSharpExercises.Lab8\",\"Name\":\"Exercise1\"},\"Attributes\":[{\"TypeId\":{\"Case\":\"Value\",\"Fields\":[{\"Namespace\":\"Microsoft.Quantum.Targeting\",\"Name\":\"RequiresCapability\",\"Range\":{\"Case\":\"Null\"}}]},\"TypeIdRange\":{\"Case\":\"Null\"},\"Argument\":{\"Item1\":{\"Case\":\"ValueTuple\",\"Fields\":[[{\"Item1\":{\"Case\":\"StringLiteral\",\"Fields\":[\"BasicQuantumFunctionality\",[]]},\"Item2\":[],\"Item3\":{\"Case\":\"String\"},\"Item4\":{\"IsMutable\":false,\"HasLocalQuantumDependency\":false},\"Item5\":{\"Case\":\"Null\"}},{\"Item1\":{\"Case\":\"StringLiteral\",\"Fields\":[\"Inferred automatically by the compiler.\",[]]},\"Item2\":[],\"Item3\":{\"Case\":\"String\"},\"Item4\":{\"IsMutable\":false,\"HasLocalQuantumDependency\":false},\"Item5\":{\"Case\":\"Null\"}}]]},\"Item2\":[],\"Item3\":{\"Case\":\"TupleType\",\"Fields\":[[{\"Case\":\"String\"},{\"Case\":\"String\"}]]},\"Item4\":{\"IsMutable\":false,\"HasLocalQuantumDependency\":false},\"Item5\":{\"Case\":\"Null\"}},\"Offset\":{\"Item1\":0,\"Item2\":0},\"Comments\":{\"OpeningComments\":[],\"ClosingComments\":[]}}],\"Modifiers\":{\"Access\":{\"Case\":\"DefaultAccess\"}},\"SourceFile\":\"/Users/jmetzger/Library/CloudStorage/OneDrive-TheMITRECorporation/Documents/Education/Introduction-to-Quantum-Software-Development/exercises/QSharpExercises/Lab8.qs\",\"Position\":{\"Item1\":24,\"Item2\":4},\"SymbolRange\":{\"Item1\":{\"Line\":1,\"Column\":11},\"Item2\":{\"Line\":1,\"Column\":20}},\"ArgumentTuple\":{\"Case\":\"QsTuple\",\"Fields\":[[{\"Case\":\"QsTupleItem\",\"Fields\":[{\"VariableName\":{\"Case\":\"ValidName\",\"Fields\":[\"register\"]},\"Type\":{\"Case\":\"UserDefinedType\",\"Fields\":[{\"Namespace\":\"Microsoft.Quantum.Arithmetic\",\"Name\":\"BigEndian\",\"Range\":{\"Case\":\"Value\",\"Fields\":[{\"Item1\":{\"Line\":1,\"Column\":33},\"Item2\":{\"Line\":1,\"Column\":42}}]}}]},\"InferredInformation\":{\"IsMutable\":false,\"HasLocalQuantumDependency\":false},\"Position\":{\"Case\":\"Null\"},\"Range\":{\"Item1\":{\"Line\":1,\"Column\":22},\"Item2\":{\"Line\":1,\"Column\":30}}}]}]]},\"Signature\":{\"TypeParameters\":[],\"ArgumentType\":{\"Case\":\"UserDefinedType\",\"Fields\":[{\"Namespace\":\"Microsoft.Quantum.Arithmetic\",\"Name\":\"BigEndian\",\"Range\":{\"Case\":\"Null\"}}]},\"ReturnType\":{\"Case\":\"UnitType\"},\"Information\":{\"Characteristics\":{\"Case\":\"Union\",\"Fields\":[{\"Case\":\"SimpleSet\",\"Fields\":[{\"Case\":\"Adjointable\"}]},{\"Case\":\"SimpleSet\",\"Fields\":[{\"Case\":\"Controllable\"}]}]},\"InferredInformation\":{\"IsSelfAdjoint\":false,\"IsIntrinsic\":false}}},\"Documentation\":[\" # Summary\",\" In this exercise, you must implement the Quantum Fourier Transform\",\" circuit. This will perform an in-place transformation of the\",\" amplitudes of each state in the superposition from the\",\" value-versus-time to the value-versus-frequency domain.\",\"\",\" # Input\",\" ## register\",\" A register containing qubits in superposition.\",\" The superposition is unknown, and the amplitudes are not guaranteed to\",\" be uniform.\"]}")]
[assembly: SpecializationDeclaration("{\"Kind\":{\"Case\":\"QsBody\"},\"TypeArguments\":{\"Case\":\"Null\"},\"Information\":{\"Characteristics\":{\"Case\":\"Union\",\"Fields\":[{\"Case\":\"SimpleSet\",\"Fields\":[{\"Case\":\"Adjointable\"}]},{\"Case\":\"SimpleSet\",\"Fields\":[{\"Case\":\"Controllable\"}]}]},\"InferredInformation\":{\"IsSelfAdjoint\":false,\"IsIntrinsic\":false}},\"Parent\":{\"Namespace\":\"QSharpExercises.Lab8\",\"Name\":\"Exercise1\"},\"Attributes\":[],\"SourceFile\":\"/Users/jmetzger/Library/CloudStorage/OneDrive-TheMITRECorporation/Documents/Education/Introduction-to-Quantum-Software-Development/exercises/QSharpExercises/Lab8.qs\",\"Position\":{\"Item1\":24,\"Item2\":4},\"HeaderRange\":{\"Item1\":{\"Line\":1,\"Column\":11},\"Item2\":{\"Line\":1,\"Column\":20}},\"Documentation\":[]}")]
[assembly: SpecializationDeclaration("{\"Kind\":{\"Case\":\"QsAdjoint\"},\"TypeArguments\":{\"Case\":\"Null\"},\"Information\":{\"Characteristics\":{\"Case\":\"Union\",\"Fields\":[{\"Case\":\"SimpleSet\",\"Fields\":[{\"Case\":\"Adjointable\"}]},{\"Case\":\"SimpleSet\",\"Fields\":[{\"Case\":\"Controllable\"}]}]},\"InferredInformation\":{\"IsSelfAdjoint\":false,\"IsIntrinsic\":false}},\"Parent\":{\"Namespace\":\"QSharpExercises.Lab8\",\"Name\":\"Exercise1\"},\"Attributes\":[],\"SourceFile\":\"/Users/jmetzger/Library/CloudStorage/OneDrive-TheMITRECorporation/Documents/Education/Introduction-to-Quantum-Software-Development/exercises/QSharpExercises/Lab8.qs\",\"Position\":{\"Item1\":24,\"Item2\":4},\"HeaderRange\":{\"Item1\":{\"Line\":1,\"Column\":54},\"Item2\":{\"Line\":1,\"Column\":63}},\"Documentation\":[\"automatically generated QsAdjoint specialization for QSharpExercises.Lab8.Exercise1\"]}")]
[assembly: SpecializationDeclaration("{\"Kind\":{\"Case\":\"QsControlled\"},\"TypeArguments\":{\"Case\":\"Null\"},\"Information\":{\"Characteristics\":{\"Case\":\"Union\",\"Fields\":[{\"Case\":\"SimpleSet\",\"Fields\":[{\"Case\":\"Adjointable\"}]},{\"Case\":\"SimpleSet\",\"Fields\":[{\"Case\":\"Controllable\"}]}]},\"InferredInformation\":{\"IsSelfAdjoint\":false,\"IsIntrinsic\":false}},\"Parent\":{\"Namespace\":\"QSharpExercises.Lab8\",\"Name\":\"Exercise1\"},\"Attributes\":[],\"SourceFile\":\"/Users/jmetzger/Library/CloudStorage/OneDrive-TheMITRECorporation/Documents/Education/Introduction-to-Quantum-Software-Development/exercises/QSharpExercises/Lab8.qs\",\"Position\":{\"Item1\":24,\"Item2\":4},\"HeaderRange\":{\"Item1\":{\"Line\":1,\"Column\":54},\"Item2\":{\"Line\":1,\"Column\":63}},\"Documentation\":[\"automatically generated QsControlled specialization for QSharpExercises.Lab8.Exercise1\"]}")]
[assembly: SpecializationDeclaration("{\"Kind\":{\"Case\":\"QsControlledAdjoint\"},\"TypeArguments\":{\"Case\":\"Null\"},\"Information\":{\"Characteristics\":{\"Case\":\"Union\",\"Fields\":[{\"Case\":\"SimpleSet\",\"Fields\":[{\"Case\":\"Adjointable\"}]},{\"Case\":\"SimpleSet\",\"Fields\":[{\"Case\":\"Controllable\"}]}]},\"InferredInformation\":{\"IsSelfAdjoint\":false,\"IsIntrinsic\":false}},\"Parent\":{\"Namespace\":\"QSharpExercises.Lab8\",\"Name\":\"Exercise1\"},\"Attributes\":[],\"SourceFile\":\"/Users/jmetzger/Library/CloudStorage/OneDrive-TheMITRECorporation/Documents/Education/Introduction-to-Quantum-Software-Development/exercises/QSharpExercises/Lab8.qs\",\"Position\":{\"Item1\":24,\"Item2\":4},\"HeaderRange\":{\"Item1\":{\"Line\":1,\"Column\":54},\"Item2\":{\"Line\":1,\"Column\":63}},\"Documentation\":[\"automatically generated QsControlledAdjoint specialization for QSharpExercises.Lab8.Exercise1\"]}")]
[assembly: CallableDeclaration("{\"Kind\":{\"Case\":\"Operation\"},\"QualifiedName\":{\"Namespace\":\"QSharpExercises.Lab8\",\"Name\":\"Exercise2\"},\"Attributes\":[{\"TypeId\":{\"Case\":\"Value\",\"Fields\":[{\"Namespace\":\"Microsoft.Quantum.Targeting\",\"Name\":\"RequiresCapability\",\"Range\":{\"Case\":\"Null\"}}]},\"TypeIdRange\":{\"Case\":\"Null\"},\"Argument\":{\"Item1\":{\"Case\":\"ValueTuple\",\"Fields\":[[{\"Item1\":{\"Case\":\"StringLiteral\",\"Fields\":[\"BasicQuantumFunctionality\",[]]},\"Item2\":[],\"Item3\":{\"Case\":\"String\"},\"Item4\":{\"IsMutable\":false,\"HasLocalQuantumDependency\":false},\"Item5\":{\"Case\":\"Null\"}},{\"Item1\":{\"Case\":\"StringLiteral\",\"Fields\":[\"Inferred automatically by the compiler.\",[]]},\"Item2\":[],\"Item3\":{\"Case\":\"String\"},\"Item4\":{\"IsMutable\":false,\"HasLocalQuantumDependency\":false},\"Item5\":{\"Case\":\"Null\"}}]]},\"Item2\":[],\"Item3\":{\"Case\":\"TupleType\",\"Fields\":[[{\"Case\":\"String\"},{\"Case\":\"String\"}]]},\"Item4\":{\"IsMutable\":false,\"HasLocalQuantumDependency\":false},\"Item5\":{\"Case\":\"Null\"}},\"Offset\":{\"Item1\":0,\"Item2\":0},\"Comments\":{\"OpeningComments\":[],\"ClosingComments\":[]}}],\"Modifiers\":{\"Access\":{\"Case\":\"DefaultAccess\"}},\"SourceFile\":\"/Users/jmetzger/Library/CloudStorage/OneDrive-TheMITRECorporation/Documents/Education/Introduction-to-Quantum-Software-Development/exercises/QSharpExercises/Lab8.qs\",\"Position\":{\"Item1\":59,\"Item2\":4},\"SymbolRange\":{\"Item1\":{\"Line\":1,\"Column\":11},\"Item2\":{\"Line\":1,\"Column\":20}},\"ArgumentTuple\":{\"Case\":\"QsTuple\",\"Fields\":[[{\"Case\":\"QsTupleItem\",\"Fields\":[{\"VariableName\":{\"Case\":\"ValidName\",\"Fields\":[\"register\"]},\"Type\":{\"Case\":\"UserDefinedType\",\"Fields\":[{\"Namespace\":\"Microsoft.Quantum.Arithmetic\",\"Name\":\"BigEndian\",\"Range\":{\"Case\":\"Value\",\"Fields\":[{\"Item1\":{\"Line\":2,\"Column\":20},\"Item2\":{\"Line\":2,\"Column\":29}}]}}]},\"InferredInformation\":{\"IsMutable\":false,\"HasLocalQuantumDependency\":false},\"Position\":{\"Case\":\"Null\"},\"Range\":{\"Item1\":{\"Line\":2,\"Column\":9},\"Item2\":{\"Line\":2,\"Column\":17}}}]},{\"Case\":\"QsTupleItem\",\"Fields\":[{\"VariableName\":{\"Case\":\"ValidName\",\"Fields\":[\"sampleRate\"]},\"Type\":{\"Case\":\"Double\"},\"InferredInformation\":{\"IsMutable\":false,\"HasLocalQuantumDependency\":false},\"Position\":{\"Case\":\"Null\"},\"Range\":{\"Item1\":{\"Line\":3,\"Column\":9},\"Item2\":{\"Line\":3,\"Column\":19}}}]}]]},\"Signature\":{\"TypeParameters\":[],\"ArgumentType\":{\"Case\":\"TupleType\",\"Fields\":[[{\"Case\":\"UserDefinedType\",\"Fields\":[{\"Namespace\":\"Microsoft.Quantum.Arithmetic\",\"Name\":\"BigEndian\",\"Range\":{\"Case\":\"Null\"}}]},{\"Case\":\"Double\"}]]},\"ReturnType\":{\"Case\":\"Double\"},\"Information\":{\"Characteristics\":{\"Case\":\"EmptySet\"},\"InferredInformation\":{\"IsSelfAdjoint\":false,\"IsIntrinsic\":false}}},\"Documentation\":[\" # Summary\",\" In this exercise, you are given a quantum register in an unknown\",\" superposition. In this superposition, a single sine wave has been\",\" encoded into the amplitudes of each term in the superposition.\",\"\",\" For example: the first sample of the wave will be the amplitude of the\",\" |0> term, the second sample of the wave will be the amplitude of the\",\" |1> term, the third will be the amplitude of the |2> term, and so on.\",\"\",\" Your goal is to find the frequency of these samples, and return that\",\" frequency.\",\"\",\" # Input\",\" ## register\",\" The register which contains the samples of the sine wave in the\",\" amplitudes of  its terms.\",\"\",\" ## sampleRate\",\" The number of samples per second that were used to collect the\",\" original samples. You will need this to retrieve the correct\",\" frequency.\",\"\",\" # Output\",\" The frequency of the sine wave.\"]}")]
[assembly: SpecializationDeclaration("{\"Kind\":{\"Case\":\"QsBody\"},\"TypeArguments\":{\"Case\":\"Null\"},\"Information\":{\"Characteristics\":{\"Case\":\"EmptySet\"},\"InferredInformation\":{\"IsSelfAdjoint\":false,\"IsIntrinsic\":false}},\"Parent\":{\"Namespace\":\"QSharpExercises.Lab8\",\"Name\":\"Exercise2\"},\"Attributes\":[],\"SourceFile\":\"/Users/jmetzger/Library/CloudStorage/OneDrive-TheMITRECorporation/Documents/Education/Introduction-to-Quantum-Software-Development/exercises/QSharpExercises/Lab8.qs\",\"Position\":{\"Item1\":59,\"Item2\":4},\"HeaderRange\":{\"Item1\":{\"Line\":1,\"Column\":11},\"Item2\":{\"Line\":1,\"Column\":20}},\"Documentation\":[]}")]
#line hidden
namespace QSharpExercises.Lab8
{
    [SourceLocation("/Users/jmetzger/Library/CloudStorage/OneDrive-TheMITRECorporation/Documents/Education/Introduction-to-Quantum-Software-Development/exercises/QSharpExercises/Lab8.qs", OperationFunctor.Body, 25, 60)]
    [SourceLocation("/Users/jmetzger/Library/CloudStorage/OneDrive-TheMITRECorporation/Documents/Education/Introduction-to-Quantum-Software-Development/exercises/QSharpExercises/Lab8.qs", OperationFunctor.Adjoint, 25, 60)]
    [SourceLocation("/Users/jmetzger/Library/CloudStorage/OneDrive-TheMITRECorporation/Documents/Education/Introduction-to-Quantum-Software-Development/exercises/QSharpExercises/Lab8.qs", OperationFunctor.Controlled, 25, 60)]
    [SourceLocation("/Users/jmetzger/Library/CloudStorage/OneDrive-TheMITRECorporation/Documents/Education/Introduction-to-Quantum-Software-Development/exercises/QSharpExercises/Lab8.qs", OperationFunctor.ControlledAdjoint, 25, 60)]
    public partial class Exercise1 : Unitary<Microsoft.Quantum.Arithmetic.BigEndian>, ICallable
    {
        public Exercise1(IOperationFactory m) : base(m)
        {
        }

        String ICallable.Name => "Exercise1";
        String ICallable.FullName => "QSharpExercises.Lab8.Exercise1";
        public override Func<Microsoft.Quantum.Arithmetic.BigEndian, QVoid> __Body__ => (__in__) =>
        {
            var register = __in__;
#line 32 "/Users/jmetzger/Library/CloudStorage/OneDrive-TheMITRECorporation/Documents/Education/Introduction-to-Quantum-Software-Development/exercises/QSharpExercises/Lab8.qs"
            throw new ExecutionFailException("Not implemented.");
#line hidden
            return QVoid.Instance;
        }

        ;
        public override Func<Microsoft.Quantum.Arithmetic.BigEndian, QVoid> __AdjointBody__ => (__in__) =>
        {
            var register = __in__;
#line 25 "/Users/jmetzger/Library/CloudStorage/OneDrive-TheMITRECorporation/Documents/Education/Introduction-to-Quantum-Software-Development/exercises/QSharpExercises/Lab8.qs"
            throw new ExecutionFailException("Not implemented.");
#line hidden
            return QVoid.Instance;
        }

        ;
        public override Func<(IQArray<Qubit>,Microsoft.Quantum.Arithmetic.BigEndian), QVoid> __ControlledBody__ => (__in__) =>
        {
            var (__controlQubits__,register) = __in__;
#line 25 "/Users/jmetzger/Library/CloudStorage/OneDrive-TheMITRECorporation/Documents/Education/Introduction-to-Quantum-Software-Development/exercises/QSharpExercises/Lab8.qs"
            throw new ExecutionFailException("Not implemented.");
#line hidden
            return QVoid.Instance;
        }

        ;
        public override Func<(IQArray<Qubit>,Microsoft.Quantum.Arithmetic.BigEndian), QVoid> __ControlledAdjointBody__ => (__in__) =>
        {
            var (__controlQubits__,register) = __in__;
#line 25 "/Users/jmetzger/Library/CloudStorage/OneDrive-TheMITRECorporation/Documents/Education/Introduction-to-Quantum-Software-Development/exercises/QSharpExercises/Lab8.qs"
            throw new ExecutionFailException("Not implemented.");
#line hidden
            return QVoid.Instance;
        }

        ;
        public override void __Init__()
        {
        }

        public override IApplyData __DataIn__(Microsoft.Quantum.Arithmetic.BigEndian data) => data;
        public override IApplyData __DataOut__(QVoid data) => data;
        public static System.Threading.Tasks.Task<QVoid> Run(IOperationFactory __m__, Microsoft.Quantum.Arithmetic.BigEndian register)
        {
            return __m__.Run<Exercise1, Microsoft.Quantum.Arithmetic.BigEndian, QVoid>(register);
        }
    }

    [SourceLocation("/Users/jmetzger/Library/CloudStorage/OneDrive-TheMITRECorporation/Documents/Education/Introduction-to-Quantum-Software-Development/exercises/QSharpExercises/Lab8.qs", OperationFunctor.Body, 60, -1)]
    public partial class Exercise2 : Operation<(Microsoft.Quantum.Arithmetic.BigEndian,Double), Double>, ICallable
    {
        public Exercise2(IOperationFactory m) : base(m)
        {
        }

        public class In : QTuple<(Microsoft.Quantum.Arithmetic.BigEndian,Double)>, IApplyData
        {
            public In((Microsoft.Quantum.Arithmetic.BigEndian,Double) data) : base(data)
            {
            }

            System.Collections.Generic.IEnumerable<Qubit> IApplyData.Qubits
            {
                get
                {
                    return ((IApplyData)Data.Item1?.Data)?.Qubits;
                }
            }
        }

        String ICallable.Name => "Exercise2";
        String ICallable.FullName => "QSharpExercises.Lab8.Exercise2";
        public override Func<(Microsoft.Quantum.Arithmetic.BigEndian,Double), Double> __Body__ => (__in__) =>
        {
            var (register,sampleRate) = __in__;
#line 65 "/Users/jmetzger/Library/CloudStorage/OneDrive-TheMITRECorporation/Documents/Education/Introduction-to-Quantum-Software-Development/exercises/QSharpExercises/Lab8.qs"
            throw new ExecutionFailException("Not implemented.");
        }

        ;
        public override void __Init__()
        {
        }

        public override IApplyData __DataIn__((Microsoft.Quantum.Arithmetic.BigEndian,Double) data) => new In(data);
        public override IApplyData __DataOut__(Double data) => new QTuple<Double>(data);
        public static System.Threading.Tasks.Task<Double> Run(IOperationFactory __m__, Microsoft.Quantum.Arithmetic.BigEndian register, Double sampleRate)
        {
            return __m__.Run<Exercise2, (Microsoft.Quantum.Arithmetic.BigEndian,Double), Double>((register, sampleRate));
        }
    }
}