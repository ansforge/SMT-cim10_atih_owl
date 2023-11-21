package fr.gouv.esante.smt.utils;


import static fr.gouv.esante.smt.utils.NameSpace.BuiltIn.BUILT_IN;
import static fr.gouv.esante.smt.utils.NameSpace.BuiltIn.NOT_BUILT_IN;
import static fr.gouv.esante.smt.utils.NameSpace.Status.IN_USE;

import org.semanticweb.owlapi.model.IRI;

/**
 * @author Matthew Horridge, The University Of Manchester, Bio-Health Informatics Group
 * @since 2.0.0
 */
public enum NameSpace {



  /** The ICD namespace. */
  ICD("icd", "http://id.who.int/icd/schema/"),
  /** The XKOS namespace. */
  XKOS("xkos", "http://rdf-vocabulary.ddialliance.org/xkos#"),
  /** The ATIHCIM10 namespace. */
  ATIHCIM10("atih-cim10", "http://data.esante.gouv.fr/atih-cim10#"),
  /** The NS namespace. */
  NS("ns", "https://data.esante.gouv.fr/profile/ns#"),
  /** The VOAF namespace. */
  VOAF("voaf", "http://purl.org/vocommons/voaf#"),
  /** The CORE namespace. */
  CORE("core", "http://open-services.net/ns/core#"),
  
  MOD("mod", "http://www.isibang.ac.in/ns/mod#"),
  
  OMV("omv", "http://omv.ontoware.org/2005/05/ontology#"),
  
  PAV("pav", "http://purl.org/pav/"),
  
  DOOR("door", "http://kannel.open.ac.uk/ontology#"),
  
  DCT("dct", "http://purl.org/dc/terms/"),
  
  VANN("vann", "http://purl.org/vocab/vann/"),
  /** The ADMS namespace. */
  ADMS("adms", "http://www.w3.org/ns/adms#");



  final Status status;
  final BuiltIn builtIn;
  final String hashless;
  private final String prefix;
  private final String ns;

  NameSpace(final String prefix, final String ns) {
    this(prefix, ns, IN_USE, NOT_BUILT_IN);
  }

  NameSpace(final String prefix, final String ns, final Status status) {
    this(prefix, ns, status, status == Status.LEGACY ? NOT_BUILT_IN : BUILT_IN);
  }

  NameSpace(final String prefix, final String ns, final Status status, final BuiltIn builtIn) {
    this.prefix = prefix;
    this.ns = ns;
    this.status = status;
    this.builtIn = builtIn;
    this.hashless = hashless(prefix);
  }

  /**
   * @param ns namespace
   * @return this namespace without hash or slash at the end
   */
  private static String hashless(final String ns) {
    final int index = ns.length() - 1;
    if ((ns.charAt(index) == '/') || (ns.charAt(index) == '#')) {
      return ns.substring(0, index);
    }
    return ns;
  }


  /**
   * @return A short, human-readable, prefix name that matches, and expands to the full IRI.
   */
  public String getPrefixName() {
    return this.prefix;
  }

  /**
   * @return The prefix IRI which matches the prefix name.
   */
  public String getPrefixIRI() {
    return this.ns;
  }

  /**
   * @return {@code true} if this namespace is not obsolete and is currently in active use,
   *         otherwise {@code false}.
   */
  public boolean isInUse() {
    return this.status == IN_USE;
  }

  /**
   * @return {@code true} if this namespace is defined as a core part of the OWL-2 specification,
   *         otherwise {@code false}.
   */
  public boolean isBuiltIn() {
    return this.builtIn == BUILT_IN;
  }

  @Override
  public String toString() {
    return this.ns;
  }

  /**
   * @param s string to check
   * @return true if s equals this namespace
   */
  public boolean inNamespace(final String s) {
    return this.ns.equals(s);
  }

  /**
   * @param i iri to check
   * @return true if the namespace for i equals this namespace
   */
  public boolean inNamespace(final IRI i) {
    return this.ns.equals(i.getNamespace());
  }

  /**
   * Indicates that a prefix is builtin - i.e. that it is either owl, rdf, rdfs, or xsd
   */
  public enum BuiltIn {
    /**
     * built in flag.
     */
    BUILT_IN,
    /**
     * not built in flag.
     */
    NOT_BUILT_IN
  }

  /**
   * Indicates whether a prefix is a legacy prefix or not.
   */
  public enum Status {
    /**
     * legacy flag.
     */
    LEGACY,
    /**
     * in use flag.
     */
    IN_USE
  }
}
