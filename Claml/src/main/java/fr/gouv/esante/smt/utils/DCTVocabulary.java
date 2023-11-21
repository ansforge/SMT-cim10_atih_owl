package fr.gouv.esante.smt.utils;

import static org.semanticweb.owlapi.model.EntityType.ANNOTATION_PROPERTY;
import static org.semanticweb.owlapi.model.EntityType.CLASS;
import static org.semanticweb.owlapi.model.EntityType.DATA_PROPERTY;
import static org.semanticweb.owlapi.model.EntityType.OBJECT_PROPERTY;
import static org.semanticweb.owlapi.util.OWLAPIStreamUtils.asSet;
import java.util.Set;
import java.util.stream.Stream;
import org.semanticweb.owlapi.model.EntityType;
import org.semanticweb.owlapi.model.HasIRI;
import org.semanticweb.owlapi.model.HasPrefixedName;
import org.semanticweb.owlapi.model.HasShortForm;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAnnotationProperty;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLDataProperty;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.providers.AnnotationPropertyProvider;



public enum DCTVocabulary implements HasShortForm, HasIRI, HasPrefixedName {
//@formatter:off
    /** alternative.         */ alternative            ("alternative",            ANNOTATION_PROPERTY),
    /** description.         */  description          ("description",            ANNOTATION_PROPERTY),
    /** license.      */  license          ("license",            ANNOTATION_PROPERTY),
    /** audience.       */  audience          ("audience",            ANNOTATION_PROPERTY),
    /** identifier.             */  identifier          ("identifier",            ANNOTATION_PROPERTY),
    /** issued.         */ issued            ("issued",            ANNOTATION_PROPERTY),
    /** language.         */  language          ("language",            ANNOTATION_PROPERTY),
    /** publisher.      */  publisher          ("publisher",            ANNOTATION_PROPERTY),
    /** relation.       */  relation          ("relation",            ANNOTATION_PROPERTY),
    /** title.             */  title          ("title",            ANNOTATION_PROPERTY),
    /** type.             */  type          ("type",            ANNOTATION_PROPERTY),
    /** accessRights.             */  accessRights          ("accessRights",            ANNOTATION_PROPERTY),
    /** contributor.             */  contributor          ("contributor",            ANNOTATION_PROPERTY),
    /** coverage.             */  coverage          ("coverage",            ANNOTATION_PROPERTY),
    /** created.             */  created          ("created",            ANNOTATION_PROPERTY),
    /** creator.             */  creator          ("creator",            ANNOTATION_PROPERTY),
    /** hasFormat.             */  hasFormat          ("hasFormat",            ANNOTATION_PROPERTY),
    /** isFormatOf.             */  isFormatOf          ("isFormatOf",            ANNOTATION_PROPERTY),
    /** rights.             */  rights          ("rights",            ANNOTATION_PROPERTY),
    /** subject.             */  subject          ("subject",            ANNOTATION_PROPERTY),
    /** source.             */  source          ("source",            ANNOTATION_PROPERTY),
    

    /** @deprecated No longer used */
    DOCUMENT("Document", CLASS),
    /** @deprecated No longer used */
    IMAGE("Image", CLASS),
    /** @deprecated No longer used */
    COLLECTABLEPROPERTY("CollectableProperty", ANNOTATION_PROPERTY),
    /** @deprecated No longer used */
    RESOURCE("Resource", CLASS),
    /** @deprecated No longer used */
    COMMENT("comment", ANNOTATION_PROPERTY);
//@formatter:on
  /**
   * All IRIs.
   */
  public static final Set<IRI> ALL_IRIS = asSet(stream().map(v -> v.getIRI()));
  private final String localName;
  private final IRI iri;
  private final EntityType<?> entityType;
  private final String prefixedName;

  DCTVocabulary(final String localname, final EntityType<?> entityType) {
    this.localName = localname;
    this.prefixedName = NameSpace.DCT.getPrefixName() + ':' + localname;
    this.entityType = entityType;
    this.iri = IRI.create(NameSpace.DCT.toString(), localname);
  }

  private static Stream<DCTVocabulary> stream() {
    return Stream.of(values());
  }

  /**
   * @param dataFactory data factory to use
   * @return set of SCHEMA annotation properties
   */
  public static Set<OWLAnnotationProperty> getAnnotationProperties(
      final AnnotationPropertyProvider dataFactory) {
    return asSet(stream().filter(v -> v.entityType.equals(ANNOTATION_PROPERTY))
        .map(v -> dataFactory.getOWLAnnotationProperty(v.iri)));
  }

  /**
   * @param dataFactory data factory to use
   * @return set of SCHEMA object properties
   */
  public static Set<OWLObjectProperty> getObjectProperties(final OWLDataFactory dataFactory) {
    return asSet(stream().filter(v -> v.entityType.equals(OBJECT_PROPERTY))
        .map(v -> dataFactory.getOWLObjectProperty(v.iri)));
  }

  /**
   * @param dataFactory data factory to use
   * @return set of SCHEMA data properties
   */
  public static Set<OWLDataProperty> getDataProperties(final OWLDataFactory dataFactory) {
    return asSet(stream().filter(v -> v.entityType.equals(DATA_PROPERTY))
        .map(v -> dataFactory.getOWLDataProperty(v.iri)));
  }

  /**
   * @param dataFactory data factory to use
   * @return set of SCHEMA classes
   */
  public static Set<OWLClass> getClasses(final OWLDataFactory dataFactory) {
    return asSet(
        stream().filter(v -> v.entityType.equals(CLASS)).map(v -> dataFactory.getOWLClass(v.iri)));
  }

  /**
   * @return entity type
   */
  public EntityType<?> getEntityType() {
    return this.entityType;
  }

  /**
   * @return local name
   */
  public String getLocalName() {
    return this.localName;
  }

  @Override
  public IRI getIRI() {
    return this.iri;
  }

  @Override
  public String getShortForm() {
    return this.localName;
  }

  @Override
  public String getPrefixedName() {
    return this.prefixedName;
  }
}
